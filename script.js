/* =========================================================
   モールス信号音声認識Webサービス（FFT・高周波特化仕様版）
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
  targetFrequency: 800,      // 狙いたいモールス信号の周波数 (Hz) ※必要に応じて調整 (例: 700〜1000など)
  frequencyTolerance: 150,   // ターゲット周波数の許容ズレ幅 (±Hz)
  minDecibels: -45,          // 音声と判定する信号強度のしきい値 (dB)
  dotDashRatio: 2.0,         // 短点・長点の判定比率（1単位と3単位の境目）
  characterGapMultiplier: 2, // 文字間の無音倍率（要素間1単位と文字間3単位の境目）
  wordGapMultiplier: 5,      // 単語間の無音倍率（文字間3単位と単語間7単位の境目）
  fftSize: 1024,             // FFTの窓（48kHzで約21ms。短いほど音の切れ目に早く反応する）
  windowBiasRatio: 0.9,      // FFT窓の分だけ音が長く・無音が短く測られるのを補正する割合
  minToneSeconds: 0.03,      // これより短い音はノイズとして無視
  defaultUnitSeconds: 0.1    // 1単位（短点）の初期値。受信しながら自動で更新する
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

// 時間はフレーム数ではなく実際の時刻（ms）で測る
let toneStartTime = null;
let silenceStartTime = null;
let symbolSequence = "";
let symbolGaps = [];
let recentUnits = [];          // 最近の音・無音から逆算した「1単位」の長さ（秒）
let hasTextSinceSpace = false; // 単語間スペースを入れてよいか（文字が出た後だけ）

function appendText(text) {
  const placeholder = recognizedText.querySelector(".placeholder");
  if (placeholder) placeholder.remove();
  
  if (recognizedText.textContent.includes("READY")) {
    recognizedText.textContent = text;
  } else {
    recognizedText.append(document.createTextNode(text));
  }
}

// 1単位（短点の長さ）の推定値。短点・長点・要素間の無音をすべて1単位に換算して中央値を取る
function getEstimatedDotDuration() {
  if (recentUnits.length === 0) return CONFIG.defaultUnitSeconds;
  const sorted = [...recentUnits].sort((a, b) => a - b);
  return Math.max(0.03, Math.min(0.3, sorted[Math.floor(sorted.length / 2)]));
}

function pushUnitSample(seconds) {
  recentUnits.push(seconds);
  if (recentUnits.length > 15) recentUnits.shift();
}

function durationToSymbol(duration) {
  const isDash = duration > getEstimatedDotDuration() * CONFIG.dotDashRatio;
  pushUnitSample(isDash ? duration / 3 : duration);
  return isDash ? "-" : ".";
}

// FFTは過去の窓をまとめて見るため、音は窓の長さぶん長く、無音はそのぶん短く測られる
function getWindowBiasSeconds() {
  return (CONFIG.fftSize / audioContext.sampleRate) * CONFIG.windowBiasRatio;
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
  hasTextSinceSpace = true;
  symbolSequence = "";
  symbolGaps = [];
}

// FFTの周波数ビンから、特定周波数帯のエネルギー（dB）を抽出する関数
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
  const frequencyData = new Float32Array(analyser.frequencyBinCount);
  analyser.getFloatFrequencyData(frequencyData);

  const peakDb = checkTargetFrequencyPower(analyser, frequencyData, audioContext.sampleRate);
  const isTone = peakDb >= CONFIG.minDecibels;
  const bias = getWindowBiasSeconds();

  if (isTone) {
    if (toneStartTime === null) {
      toneStartTime = now;
      if (silenceStartTime !== null && symbolSequence.length > 0) {
        const gap = (now - silenceStartTime) / 1000 + bias;
        symbolGaps.push(gap);
        // 要素間の無音（約1単位）も1単位の推定に使う
        if (gap < getEstimatedDotDuration() * CONFIG.characterGapMultiplier) pushUnitSample(gap);
      }
      silenceStartTime = null;
    }
  } else {
    if (toneStartTime !== null) {
      const toneDuration = (now - toneStartTime) / 1000 - bias;
      if (toneDuration >= CONFIG.minToneSeconds) {
        symbolSequence += durationToSymbol(toneDuration);
      }
      toneStartTime = null;
      silenceStartTime = now;
    }
    if (silenceStartTime === null) silenceStartTime = now;

    const silenceDuration = (now - silenceStartTime) / 1000 + bias;
    const dotDuration = getEstimatedDotDuration();

    if (symbolSequence && silenceDuration >= dotDuration * CONFIG.characterGapMultiplier) {
      decodeCurrentSequence();
    }

    if (mode === "en" && !symbolSequence && hasTextSinceSpace &&
        silenceDuration >= dotDuration * CONFIG.wordGapMultiplier) {
      appendText(" ");
      hasTextSinceSpace = false;
    }
  }

  animationId = requestAnimationFrame(processFrame);
}

async function startListening() {
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    appendText("\n[このブラウザではマイク入力を利用できません]");
    toggleButton.setAttribute("aria-pressed", "false");
    return;
  }

  try {
    mediaStream = await navigator.mediaDevices.getUserMedia({
      audio: {
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false
      },
      video: false
    });

    audioContext = new (window.AudioContext || window.webkitAudioContext)();
    await audioContext.resume();

    sourceNode = audioContext.createMediaStreamSource(mediaStream);
    
    // AnalyserNodeの作成（FFTによる周波数解析）
    analyser = audioContext.createAnalyser();
    analyser.fftSize = CONFIG.fftSize; // 窓が短いほど音の切れ目を早く検出できる
    analyser.smoothingTimeConstant = 0.1; // 応答性を高めるため小さめに

    sourceNode.connect(analyser);
    // スピーカーからのハウリングを防ぐため音源はdestinationには繋がない

    resetProcessingState();
    isListening = true;
    toggleButton.textContent = "録音中";
    toggleButton.setAttribute("aria-label", "録音中。タップして停止");

    animationId = requestAnimationFrame(processFrame);

  } catch (error) {
    console.error(error);
    const reason = error.name === "NotAllowedError" ? "マイクの権限を確認してください" : error.name;
    appendText(`\n[録音を開始できませんでした: ${reason}]`);
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
  toggleButton.setAttribute("aria-pressed", "false");
}

function resetProcessingState() {
  toneStartTime = null;
  silenceStartTime = null;
  symbolSequence = "";
  symbolGaps = [];
  recentUnits = [];
  hasTextSinceSpace = false;
}

toggleButton.addEventListener("click", () => {
  if (isListening) {
    stopListening();
  } else {
    // 押した瞬間から濃い色にする（マイク許可の確認中も含む）。失敗時は stopListening で戻る
    toggleButton.setAttribute("aria-pressed", "true");
    startListening();
  }
});

window.addEventListener("pagehide", stopListening);