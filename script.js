/* =========================================================
   モールス信号音声認識Webサービス（FFT・高周波特化仕様版・iPhone対応修正）
   ========================================================= */

"use strict";

const recognizedText = document.getElementById("recognizedText");
const toggleButton = document.getElementById("toggleButton");

let audioContext = null;
let mediaStream = null;
let sourceNode = null;
let analyser = null;
let animationId = null;
let isListening = false;

let mode = "ja";
function updateMode() {
  mode = window.innerWidth > window.innerHeight ? "en" : "ja";
}
window.addEventListener("resize", updateMode);
window.addEventListener("orientationchange", updateMode);
updateMode();

// FFTおよびモールス信号検出のパラメータ
const CONFIG = {
  targetFrequency: 800,
  frequencyTolerance: 150,
  minDecibels: -45,
  dotDashRatio: 2.0,
  characterGapMultiplier: 3,
  wordGapMultiplier: 7,
  frameIntervalMs: 20
};

const INTERNATIONAL = {
  ".-":"A","-...":"B","-.-.":"C","-..":"D",".":"E","..-.":"F",
  "--.":"G","....":"H","..":"I",".---":"J","-.-":"K",".-..":"L",
  "--":"M","-.":"N","---":"O",".--.":"P","--.-":"Q",".-.":"R",
  "...":"S","-":"T","..-":"U","...-":"V",".--":"W","-..-":"X",
  "-.--":"Y","--..":"Z",
  "-----":"0",".----":"1","..---":"2","...--":"3","....-":"4",
  ".....":"5","-....":"6","--...":"7","---..":"8","----.":"9",
  ".-.-.-":".","--..--":",","..--..":"?","-.-.--":"!","-..-.":"/",
  "-.--.":"(","-.--.-":")",".-...":"&","---...":":","-.-.-.":";",
  "-...-":"=",".-.-.":"+","-....-":"-","..--.-":"_",".-..-.":"\"",
  "...-..-":"$",".--.-.":"@"
};

const JAPANESE_MORSE_CORRECT = {
  "--.--": "ア", ".-": "イ", "..-": "ウ", "-.---": "エ", ".-...": "オ",
  ".-..": "カ", "-.-..": "キ", "...-": "ク", "-.--": "ケ", "----": "コ",
  "-.-.-": "サ", "--.-.": "シ", "---.-": "ス", ".---.": "セ", "---.": "ソ",
  "-.-": "タ", "..-.": "チ", ".--.": "ツ", ".-.--": "テ", "..-..": "ト",
  ".-.": "ナ", "-.-.": "ニ", "....": "ヌ", "--.-": "ネ", "..--": "ノ",
  "-...": "ハ", "--..-": "ヒ", "--..": "フ", ".": "ヘ", "-..": "ホ",
  "-..-": "マ", "..-.-": "ミ", "-": "ム", "-...-": "メ", "-..-.": "モ",
  ".--": "ヤ", "-..--": "ユ", "--": "ヨ",
  "...": "ラ", "--.": "リ", "-.--.": "ル", "---": "レ", "-.-.": "ロ",
  "-.-": "ワ", ".---": "ヲ", ".-.-.": "ン",
  "..": "、", "..--.": "゜"
};

let toneFrames = 0;
let silenceFrames = 0;
let currentToneDuration = 0;
let symbolSequence = "";
let symbolGaps = [];
let recentToneDurations = [];

let lastFrameTime = performance.now();

function appendText(text) {
  const placeholder = recognizedText.querySelector(".placeholder");
  if (placeholder) placeholder.remove();
  
  if (recognizedText.textContent.includes("READY")) {
    recognizedText.textContent = text;
  } else {
    recognizedText.append(document.createTextNode(text));
  }
}

function getEstimatedDotDuration() {
  if (recentToneDurations.length === 0) return 0.1;
  const sorted = [...recentToneDurations].sort((a, b) => a - b);
  return Math.max(0.05, Math.min(0.25, sorted[Math.floor(sorted.length * 0.25)] || 0.1));
}

function durationToSymbol(duration) {
  const dotEstimate = getEstimatedDotDuration();
  const symbol = duration > dotEstimate * CONFIG.dotDashRatio ? "-" : ".";
  recentToneDurations.push(duration);
  if (recentToneDurations.length > 9) recentToneDurations.shift();
  return symbol;
}

function decodeSequenceWithGapRecovery(sequence, gaps, table) {
  if (!sequence) return null;
  if (Object.prototype.hasOwnProperty.call(table, sequence)) {
    return table[sequence];
  }
  if (sequence.length < 2 || gaps.length === 0) return null;

  const candidates = gaps
    .map((duration, index) => ({ duration, index }))
    .sort((a, b) => b.duration - a.duration);

  for (const candidate of candidates) {
    const splitAt = candidate.index + 1;
    const leftText = decodeSequenceWithGapRecovery(sequence.slice(0, splitAt), gaps.slice(0, candidate.index), table);
    if (leftText === null) continue;
    const rightText = decodeSequenceWithGapRecovery(sequence.slice(splitAt), gaps.slice(candidate.index + 1), table);
    if (rightText === null) continue;
    return leftText + rightText;
  }
  return null;
}

function decodeCurrentSequence() {
  if (!symbolSequence) return;
  const table = mode === "en" ? INTERNATIONAL : JAPANESE_MORSE_CORRECT;
  const decoded = decodeSequenceWithGapRecovery(symbolSequence, symbolGaps, table);
  appendText(decoded === null ? "?" : decoded);
  symbolSequence = "";
  symbolGaps = [];
}

function checkTargetFrequencyPower(analyser, frequencyData, sampleRate) {
  const binCount = analyser.frequencyBinCount;
  const nyquist = sampleRate / 2;
  
  const minFreq = CONFIG.targetFrequency - CONFIG.frequencyTolerance;
  const maxFreq = CONFIG.targetFrequency + CONFIG.frequencyTolerance;
  
  const minIndex = Math.floor((minFreq / nyquist) * binCount);
  const maxIndex = Math.floor((maxFreq / nyquist) * binCount);
  
  let maxDb = -Infinity;
  for (let i = Math.max(0, minIndex); i <= Math.min(binCount - 1, maxIndex); i++) {
    if (frequencyData[i] > maxDb) {
      maxDb = frequencyData[i];
    }
  }
  return maxDb;
}

function processFrame() {
  if (!isListening) return;

  const now = performance.now();
  const deltaTime = (now - lastFrameTime) / 1000;
  
  if (deltaTime >= CONFIG.frameIntervalMs / 1000) {
    lastFrameTime = now;

    const frequencyData = new Float32Array(analyser.frequencyBinCount);
    analyser.getFloatFrequencyData(frequencyData);

    const peakDb = checkTargetFrequencyPower(analyser, frequencyData, audioContext.sampleRate);
    const isTone = peakDb >= CONFIG.minDecibels;
    const frameDuration = deltaTime;

    if (isTone) {
      if (toneFrames === 0 && symbolSequence.length > 0 && silenceFrames > 0) {
        symbolGaps.push(silenceFrames * frameDuration);
      }
      toneFrames++;
      currentToneDuration += frameDuration;
      silenceFrames = 0;
    } else {
      if (toneFrames > 0) {
        if (toneFrames >= 2 && currentToneDuration >= 0.04) {
          symbolSequence += durationToSymbol(currentToneDuration);
        }
        toneFrames = 0;
        currentToneDuration = 0;
      }

      silenceFrames++;
      const silenceDuration = silenceFrames * frameDuration;
      const dotDuration = getEstimatedDotDuration();
      
      if (symbolSequence && silenceDuration >= dotDuration * CONFIG.characterGapMultiplier) {
        decodeCurrentSequence();
      }

      if (mode === "en" && !symbolSequence && silenceDuration >= dotDuration * CONFIG.wordGapMultiplier) {
        const currentText = recognizedText.textContent || "";
        if (currentText && !currentText.endsWith(" ")) appendText(" ");
      }
    }
  }

  animationId = requestAnimationFrame(processFrame);
}

async function startListening() {
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    appendText("\n[このブラウザではマイク入力を利用できません]");
    return;
  }

  try {
    // iPhone Safariで確実に許可を取るため、シンプルにマイクを取得
    mediaStream = await navigator.mediaDevices.getUserMedia({
      audio: {
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false
      },
      video: false
    });

    audioContext = new (window.AudioContext || window.webkitAudioContext)();
    if (audioContext.state === "suspended") {
      await audioContext.resume();
    }

    sourceNode = audioContext.createMediaStreamSource(mediaStream);
    
    analyser = audioContext.createAnalyser();
    analyser.fftSize = 2048;
    analyser.smoothingTimeConstant = 0.1;

    sourceNode.connect(analyser);

    resetProcessingState();
    isListening = true;
    toggleButton.textContent = "録音中";
    toggleButton.setAttribute("aria-label", "録音中。タップして停止");

    lastFrameTime = performance.now();
    animationId = requestAnimationFrame(processFrame);

  } catch (error) {
    appendText("\n[エラー: " + error.name + " - " + error.message + "]");
    stopListening();
  }
}

function stopListening() {
  isListening = false;
  if (animationId) {
    cancelAnimationFrame(animationId);
    animationId = null;
  }
  if (sourceNode) {
    try { sourceNode.disconnect(); } catch (_) {}
    sourceNode = null;
  }
  if (mediaStream) {
    mediaStream.getTracks().forEach(track => track.stop());
    mediaStream = null;
  }
  if (audioContext) {
    audioContext.close().catch(() => {});
    audioContext = null;
  }

  toggleButton.textContent = "録音開始";
  toggleButton.setAttribute("aria-label", "録音開始");
}

function resetProcessingState() {
  toneFrames = 0;
  silenceFrames = 0;
  currentToneDuration = 0;
  symbolSequence = "";
  symbolGaps = [];
  recentToneDurations = [];
}

toggleButton.addEventListener("click", () => {
  if (isListening) {
    stopListening();
  } else {
    startListening();
  }
});

window.addEventListener("pagehide", stopListening);
```[cite: 2]

<FollowUp>
この修正版コードを反映してiPhoneのSafari（プライベートモードなど）から再度アクセスし、ボタンを押したときに「録音中」に切り替わるか、あるいはエラー文言が出るか確認していただけますか？
</FollowUp>

<ElicitationsGroup>
</ElicitationsGroup>