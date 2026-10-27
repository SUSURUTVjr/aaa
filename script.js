/* =========================================================
   モールス信号音声認識Webサービス（ブロック処理版）
   仕様:
   ・録音中は約3秒ごとの音声ブロックを作る（可視化しない）。
   ・ブロックから音の有無、周波数候補、継続時間を抽出する。
   ・2ブロック以上そろったら、古いブロックから符号判定する。
   ・文字の途中でブロックが終わった場合は、後続ブロックの冒頭も使う。
   ・解析済みの音声サンプルは保持せず破棄する。
   ・録音データをファイル保存したり、外部送信したりしない。
   ========================================================= */

"use strict";

// 画面要素を取得します。
const recognizedText = document.getElementById("recognizedText");
const toggleButton = document.getElementById("toggleButton");

// マイクと音声処理の状態を管理します。
let audioContext = null;
let mediaStream = null;
let sourceNode = null;
let processorNode = null;
let isListening = false;

// 縦長画面では和文、横長画面では欧文モールスを使用します。
let mode = "ja";
function updateMode() {
  mode = window.innerWidth > window.innerHeight ? "en" : "ja";
}
window.addEventListener("resize", updateMode);
window.addEventListener("orientationchange", updateMode);
updateMode();

// 音声ブロックのサイズと判定の調整値です。
const CONFIG = {
  blockSeconds: 3,             // 1ブロックを約3秒にする
  frameSeconds: 0.02,          // 1ブロックを約20msごとの特徴量に分ける
  minFrequency: 250,           // 初期探索は広い周波数範囲
  maxFrequency: 3000,
  minimumLevelDb: -50,         // 小さな環境音を拾いすぎないよう閾値を上げる
  toneStartFrames: 3,          // 60ms未満の短い瞬間ノイズを抑える
  dotDashRatio: 1.8,           // 長点と短点を区別しやすくする比率
  characterGapMultiplier: 3,   // 短点の長さの約3倍で文字境界とみなす
  wordGapMultiplier: 7       // 短点の長さの約7倍で単語境界とみなす
};

// 欧文モールス符号表（英字・数字・基本記号）。
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
  // ア行
  "--.--": "ア",  ".-": "イ",     "..-": "ウ",    "-.---": "エ",  ".-...": "オ",
  // カ行
  ".-..": "カ",   "-.-..": "キ",   "...-": "ク",  "-.--": "ケ",   "----": "コ",
  // サ行
  "-.-.-": "サ",     "--.-.": "シ",   "---.-": "ス",   ".---.": "セ",  "---.": "ソ",
  // タ行
  "-.-": "タ",      "..-.": "チ",   ".--.": "ツ",   ".-.--": "テ",    "..-..": "ト",
  // ナ行
  ".-.": "ナ",   "-.-.": "ニ",   "....": "ヌ",   "--.-": "ネ",   "..--": "ノ",
  // ハ行
  "-...": "ハ",   "--..-": "ヒ",  "--..": "フ",  ".": "ヘ",  "-..": "ホ",
  // マ行
  "-..-": "マ",   "..-.-": "ミ",   "-": "ム",   "-...-": "メ",     "-..-.": "モ", // ※下記解説参照
  // ヤ行
  ".--": "ヤ",    "-..--": "ユ",    "--": "ヨ",
  // ラ行
  "...": "ラ",    "--.": "リ",    "-.--.": "ル",    "---": "レ",    "-.-.": "ロ",
  // ワ行
  "-.-": "ワ", ".---": "ヲ",   ".-.-.": "ン",
  // 記号
  "..": "、", "..--.": "゜"
};


// 約3秒分のサンプルをためるバッファと、特徴量ブロックの待ち行列です。
let sampleBuffer = [];
let samplesPerBlock = 0;
let blockQueue = [];
let blockNumber = 0;

// 連続する符号をブロック境界で失わないための解析状態です。
let toneFrames = 0;
let silenceFrames = 0;
let currentToneDuration = 0;
let currentToneFrequencySum = 0;
let currentToneFrequencyCount = 0;
let symbolSequence = "";
// 符号間の無音時間を記録し、誤って連結された文字を分割し直すために使います。
let symbolGaps = [];
let recentToneDurations = [];
let lockedFrequency = null;
let lastToneFrequency = null;

// 画面に文字を追記します。認識文字は自動で消しません。
function appendText(text) {
  const placeholder = recognizedText.querySelector(".placeholder");
  if (placeholder) placeholder.remove();
  recognizedText.append(document.createTextNode(text));
}

// サンプルのRMS値から音量を求めます。
function calculateRms(samples, start, end) {
  let sum = 0;
  for (let i = start; i < end; i++) sum += samples[i] * samples[i];
  return Math.sqrt(sum / Math.max(1, end - start));
}

// 自己相関の簡易計算で、音の周波数候補を推定します。
// 強い周期性がない音は、周波数候補を持たないものとして扱います。
function estimateFrequency(samples, start, end, sampleRate) {
  const length = end - start;
  if (length < 64) return null;

  const minLag = Math.max(2, Math.floor(sampleRate / CONFIG.maxFrequency));
  const maxLag = Math.min(Math.floor(sampleRate / CONFIG.minFrequency), Math.floor(length / 2));
  let bestLag = -1;
  let bestCorrelation = 0;

  for (let lag = minLag; lag <= maxLag; lag++) {
    let cross = 0, leftEnergy = 0, rightEnergy = 0;
    for (let i = start; i < end - lag; i++) {
      const a = samples[i];
      const b = samples[i + lag];
      cross += a * b;
      leftEnergy += a * a;
      rightEnergy += b * b;
    }
    const denom = Math.sqrt(leftEnergy * rightEnergy);
    const correlation = denom > 0 ? cross / denom : 0;
    if (correlation > bestCorrelation) {
      bestCorrelation = correlation;
      bestLag = lag;
    }
  }

  if (bestLag < 0 || bestCorrelation < 0.25) return null;
  return sampleRate / bestLag;
}

// 1ブロック分（約3秒）の音声サンプルを特徴量に変換します。
// 元のサンプルはこの関数の後、ブロックキューに保存しません。
function extractBlockFeatures(samples, sampleRate) {
  const frameSize = Math.max(256, Math.floor(sampleRate * CONFIG.frameSeconds));
  const features = [];

  for (let start = 0; start < samples.length; start += frameSize) {
    const end = Math.min(samples.length, start + frameSize);
    const rms = calculateRms(samples, start, end);
    const db = 20 * Math.log10(Math.max(rms, 1e-8));
    let frequency = null;

    // 音量が閾値を超えた区間だけ、特徴的な周波数を推定します。
    if (db >= CONFIG.minimumLevelDb) {
      frequency = estimateFrequency(samples, start, end, sampleRate);
    }

    // 音量がある場合も、周期性が弱い場合は候補音として残します。
    const isTone = db >= CONFIG.minimumLevelDb &&
      (frequency === null || (frequency >= CONFIG.minFrequency && frequency <= CONFIG.maxFrequency));

    features.push({
      tone: isTone,
      frequency,
      duration: (end - start) / sampleRate
    });
  }
  return features;
}

// 直近の音の長さから短音（dot）の基準時間を推定します。
function getEstimatedDotDuration() {
  if (recentToneDurations.length === 0) return 0.1;
  // 中央値ではなく下位側の値を使い、長点が短点の基準を押し上げないようにします。
  const sorted = [...recentToneDurations].sort((a, b) => a - b);
  const lowerQuartile = sorted[Math.floor((sorted.length - 1) * 0.25)];
  return Math.max(0.06, Math.min(0.25, lowerQuartile || 0.1));
}

// 短音・長音の長さを分類します。極端に短い音は呼び出し側で除外します。
function durationToSymbol(duration) {
  const dotEstimate = getEstimatedDotDuration();
  const symbol = duration > dotEstimate * CONFIG.dotDashRatio ? "-" : ".";
  recentToneDurations.push(duration);
  if (recentToneDurations.length > nineLimit()) recentToneDurations.shift();
  return symbol;
}
function nineLimit() { return 9; }

// 符号列を変換表で検索します。一致しない場合は、長い無音区間から順に分割を試します。
function decodeSequenceWithGapRecovery(sequence, gaps, table) {
  if (!sequence) return null;

  // まずは分割せず、符号列全体が変換表にあるか確認します。
  if (Object.prototype.hasOwnProperty.call(table, sequence)) {
    return table[sequence];
  }

  // 1文字分の符号しかない場合や、分割できる無音区間がない場合は失敗です。
  if (sequence.length < 2 || gaps.length === 0) return null;

  // 最も長い無音区間を優先し、そこを文字境界と仮定して左右を再変換します。
  const candidates = gaps
    .map((duration, index) => ({ duration, index }))
    .sort((a, b) => b.duration - a.duration);

  for (const candidate of candidates) {
    const splitAt = candidate.index + 1;
    const leftSequence = sequence.slice(0, splitAt);
    const rightSequence = sequence.slice(splitAt);
    const leftGaps = gaps.slice(0, candidate.index);
    const rightGaps = gaps.slice(candidate.index + 1);

    const leftText = decodeSequenceWithGapRecovery(leftSequence, leftGaps, table);
    if (leftText === null) continue;
    const rightText = decodeSequenceWithGapRecovery(rightSequence, rightGaps, table);
    if (rightText === null) continue;

    return leftText + rightText;
  }

  return null;
}

// 現在のモードで符号列を文字に変換します。
function decodeCurrentSequence() {
  if (!symbolSequence) return;
  const table = mode === "en" ? INTERNATIONAL : JAPANESE_MORSE_CORRECT;
  const decoded = decodeSequenceWithGapRecovery(symbolSequence, symbolGaps, table);
  appendText(decoded === null ? "?" : decoded);
  symbolSequence = "";
  symbolGaps = [];
}

// 特徴量フレームを解析し、符号と文字の境界を判定します。
// 状態変数はブロックをまたいで保持するため、途中で切れた符号を継続できます。
function consumeFeatureFrame(frame) {
  if (frame.tone) {
    // 新しい音が始まった時点で、直前の符号との無音時間を記録します。
    if (toneFrames === 0 && symbolSequence.length > 0 && silenceFrames > 0) {
      symbolGaps.push(silenceFrames * frame.duration);
    }
    // 音が続いている間、長さと周波数候補を累積します。
    toneFrames++;
    currentToneDuration += frame.duration;
    if (frame.frequency !== null) {
      currentToneFrequencySum += frame.frequency;
      currentToneFrequencyCount++;
      lastToneFrequency = frame.frequency;
    }
    silenceFrames = 0;
    return false;
  }

  // 無音になったら、直前の音を短音または長音として確定します。
  if (toneFrames > 0) {
    const toneDuration = currentToneDuration;
    if (toneFrames >= CONFIG.toneStartFrames && toneDuration >= 0.06) {
      // 60ms未満の短いクリック音などはモールス符号として採用しません。
      // 最初は周波数を限定せず、周期的な音が複数回現れた場合に音域候補を保持します。
      if (currentToneFrequencyCount > 0) {
        const averageFrequency = currentToneFrequencySum / currentToneFrequencyCount;
        if (lockedFrequency === null) lockedFrequency = averageFrequency;
        else lockedFrequency = lockedFrequency * 0.7 + averageFrequency * 0.3;
      }
      symbolSequence += durationToSymbol(toneDuration);
    }
    toneFrames = 0;
    currentToneDuration = 0;
    currentToneFrequencySum = 0;
    currentToneFrequencyCount = 0;
  }

  silenceFrames++;
  const silenceDuration = silenceFrames * frame.duration;

  // 文字間隔および単語間隔の閾値を短音の長さに比例して計算します。
  // 履歴がない場合は getEstimatedDotDuration() が 0.1 秒を返します。
  const dotDuration = getEstimatedDotDuration();
  const characterGapThreshold = dotDuration * CONFIG.characterGapMultiplier;
  const wordGapThreshold = dotDuration * CONFIG.wordGapMultiplier;

  // 文字間隔に達したら、蓄積した符号列を文字へ変換します。
  if (symbolSequence && silenceDuration >= characterGapThreshold) {
    decodeCurrentSequence();
    return true; 
  }

  // 単語間隔は欧文モードでのみスペースとして表示します。
  if (mode === "en" && !symbolSequence &&
      silenceDuration >= wordGapThreshold) {
    const currentText = recognizedText.textContent || "";
    if (currentText && !currentText.endsWith(" ")) appendText(" ");
  }
  return false;
}

// 2ブロック分がそろったら古いブロックを処理します。
// 1ブロック末尾の符号が未完了なら、次ブロックの先頭を使って文字境界まで解析します。
function processAvailableBlocks() {
  while (blockQueue.length >= 2) {
    const firstBlock = blockQueue[0];
    const secondBlock = blockQueue[1];

    // 古いブロックはすべて処理します。音声サンプルではなく特徴量だけを扱います。
    for (const feature of firstBlock.features) {
      consumeFeatureFrame(feature);
    }

    // 1ブロック目の末尾に未確定の符号列がある場合だけ、2ブロック目の冒頭も先行解析します。
    if (symbolSequence || toneFrames > 0) {
      let consumed = 0;
      for (; consumed < secondBlock.features.length; consumed++) {
        const completed = consumeFeatureFrame(secondBlock.features[consumed]);
        if (completed) {
          consumed++;
          break;
        }
      }

      // 2ブロック目の未処理部分は次回に残し、解析済みフレームは破棄します。
      secondBlock.features = secondBlock.features.slice(consumed);
      if (secondBlock.features.length === 0) blockQueue.splice(1, 1);
    }

    // 1ブロック目は完全に処理したため、音声データと特徴量を廃棄します。
    blockQueue.shift();
  }
}

// 録音開始時の状態を初期化します。
function resetProcessingState() {
  sampleBuffer = [];
  blockQueue = [];
  blockNumber = 0;
  toneFrames = 0;
  silenceFrames = 0;
  currentToneDuration = 0;
  currentToneFrequencySum = 0;
  currentToneFrequencyCount = 0;
  symbolSequence = "";
  symbolGaps = [];
  recentToneDurations = [];
  lockedFrequency = null;
  lastToneFrequency = null;
}

// 音声サンプルを連続して集め、約3秒ごとにブロック化します。
function collectSamples(inputSamples) {
  for (let i = 0; i < inputSamples.length; i++) {
    sampleBuffer.push(inputSamples[i]);
  }

  while (sampleBuffer.length >= samplesPerBlock) {
    const blockSamples = sampleBuffer.slice(0, samplesPerBlock);
    sampleBuffer = sampleBuffer.slice(samplesPerBlock);

    // 3秒ブロックから特徴量だけを抽出します。処理後に生サンプルは保持しません。
    const features = extractBlockFeatures(blockSamples, audioContext.sampleRate);
    blockNumber++;
    blockQueue.push({ number: blockNumber, features });

    // 生の音声サンプルを参照できる状態に残さず、特徴量ブロックのみで続行します。
    blockSamples.fill(0);
    processAvailableBlocks();
  }
}

// 録音を開始します。
async function startListening() {
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    appendText("\n[このブラウザではマイク入力を利用できません]");
    return;
  }

  try {
    // 音声は端末内のAudioContextに取り込み、ファイル化・送信はしません。
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
    samplesPerBlock = Math.floor(audioContext.sampleRate * CONFIG.blockSeconds);

    sourceNode = audioContext.createMediaStreamSource(mediaStream);

    // ScriptProcessorNodeでマイクサンプルを受け取り、約3秒単位にまとめます。
    // 対応ブラウザが限られる場合はAudioWorkletへの移行を検討します。
    const bufferSize = 4096;
    processorNode = audioContext.createScriptProcessor(bufferSize, 1, 1);
    processorNode.onaudioprocess = event => {
      if (!isListening) return;
      const input = event.inputBuffer.getChannelData(0);
      collectSamples(new Float32Array(input));
    };

    // 無音の出力先につなぎ、処理を継続します。出力音は発生させません。
    const silentGain = audioContext.createGain();
    silentGain.gain.value = 0;
    sourceNode.connect(processorNode);
    processorNode.connect(silentGain);
    silentGain.connect(audioContext.destination);

    resetProcessingState();
    isListening = true;
    toggleButton.textContent = "録音中";
    toggleButton.setAttribute("aria-label", "録音中。タップして停止");
  } catch (error) {
    appendText("\n[録音を開始できませんでした。マイクの権限とHTTPS接続を確認してください]");
    stopListening();
  }
}

// 録音を停止し、マイクや音声処理を解放します。
function stopListening() {
  isListening = false;

  if (processorNode) {
    processorNode.onaudioprocess = null;
    try { processorNode.disconnect(); } catch (_) {}
    processorNode = null;
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

  // 停止時に残った未確定符号列は、誤った文字確定を避けるため表示しません。
  sampleBuffer = [];
  blockQueue = [];
  toggleButton.textContent = "録音開始";
  toggleButton.setAttribute("aria-label", "録音開始");
}

// ボタンのタッチ／クリックで録音を開始・停止します。
toggleButton.addEventListener("click", () => {
  if (isListening) stopListening();
  else startListening();
});

// ページを閉じる／移動する際はマイクを解放します。
window.addEventListener("pagehide", stopListening);
