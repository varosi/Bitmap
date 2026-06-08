import Bitmap.Lemmas.Png.FixedBlockProofsCommon
import Bitmap.Lemmas.Png.FixedLiteral

universe u

namespace Bitmaps

namespace Png

def dynamicCodeLenLengths : Array Nat :=
  #[0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def dynamicCodeLenHuffman : Huffman :=
  { maxLen := 2
    table := #[
      #[],
      Array.replicate (1 <<< 1) none,
      #[some 5, some 8, some 7, some 9]
    ] }

def fixedDistRow5 : Array (Option Nat) :=
  Array.ofFn (fun i : Fin (1 <<< 5) =>
    some (reverseBits i.val 5))

def fixedDistHuffman : Huffman :=
  { maxLen := 5
    table := #[
      #[],
      Array.replicate (1 <<< 1) none,
      Array.replicate (1 <<< 2) none,
      Array.replicate (1 <<< 3) none,
      Array.replicate (1 <<< 4) none,
      fixedDistRow5
    ] }

def dynamicLitLenLengths : Array Nat :=
  (Array.replicate 144 8) ++
    (Array.replicate 112 9) ++
    (Array.replicate 24 7) ++
    (Array.replicate 8 8)

def dynamicDistLengths : Array Nat :=
  Array.replicate 32 5

def dynamicHeaderCodeLenSyms : List Nat :=
  List.replicate 144 8 ++
    List.replicate 112 9 ++
    List.replicate 24 7 ++
    List.replicate 8 8 ++
    List.replicate 32 5

def dynamicHeaderCodeLenLens : List Nat :=
  [0, 0, 0, 0, 2, 2, 2, 0, 0, 2]

def dynamicCodeLenSymRevBits (sym : Nat) : Nat :=
  if sym = 5 then 0
  else if sym = 8 then 1
  else if sym = 7 then 2
  else if sym = 9 then 3
  else 0

def dynamicCodeLenSymBits : List Nat → Nat
  | [] => 0
  | sym :: syms => dynamicCodeLenSymRevBits sym ||| (dynamicCodeLenSymBits syms <<< 2)

def dynamicHeaderPrefixBits : Nat :=
  31 ||| (31 <<< 5) ||| (6 <<< 10)

def dynamicHeaderPrefixLen : Nat := 14

def dynamicHeaderCodeLenLenBits : Nat :=
  Id.run do
    let mut bits := 0
    let mut shift := 0
    for len in dynamicHeaderCodeLenLens do
      bits := bits ||| (len <<< shift)
      shift := shift + 3
    bits

def dynamicHeaderCodeLenLen : Nat := 30

def dynamicHeaderTailBits : Nat :=
  Id.run do
    let mut bits := 0
    let mut shift := 0
    for len in dynamicHeaderCodeLenLens do
      bits := bits ||| (len <<< shift)
      shift := shift + 3
    for sym in dynamicHeaderCodeLenSyms do
      bits := bits ||| (dynamicCodeLenSymRevBits sym <<< shift)
      shift := shift + 2
    bits

def dynamicHeaderTailLen : Nat := 670

def dynamicHeaderTableBits : Nat :=
  dynamicHeaderPrefixBits ||| (dynamicHeaderTailBits <<< dynamicHeaderPrefixLen)

def dynamicHeaderTableLen : Nat := dynamicHeaderPrefixLen + dynamicHeaderTailLen

def dynamicCodeLenLengthsFilled : Array Nat :=
  Id.run do
    let order : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
    let mut codeLenLengths : Array Nat := Array.replicate 19 0
    for i in [0:dynamicHeaderCodeLenLens.length] do
      codeLenLengths := codeLenLengths.set! order[i]! (dynamicHeaderCodeLenLens[i]!)
    codeLenLengths

/-- Records the canonical code-length alphabet size so later table proofs can rewrite sizes quickly. -/
lemma dynamicCodeLenLengths_size : dynamicCodeLenLengths.size = 19 := by
  decide

/-- Fixes the emitted literal/length table width at the DEFLATE-required 288 entries. -/
lemma dynamicLitLenLengths_size : dynamicLitLenLengths.size = 288 := by
  simp [dynamicLitLenLengths]

/-- Fixes the emitted distance table width at the DEFLATE-required 32 entries. -/
lemma dynamicDistLengths_size : dynamicDistLengths.size = 32 := by
  simp [dynamicDistLengths]

/-- Expands the concrete dynamic header length into the exact bit budget used by the proof. -/
lemma dynamicHeaderTableLen_eq :
    dynamicHeaderTableLen = 5 + 5 + 4 + 10 * 3 + 320 * 2 := by
  decide

/-- Notes that the code-length stream writes one symbol for every lit/len and distance entry. -/
lemma dynamicHeaderCodeLenSyms_length :
    dynamicHeaderCodeLenSyms.length = 320 := by
  native_decide

/-- Identifies the fixed ten code-length lengths written by the dynamic header. -/
lemma dynamicHeaderCodeLenLen_eq :
    dynamicHeaderCodeLenLen = 10 * 3 := by
  decide

/-- Splits the dynamic header tail into the code-length-length prefix and the symbol stream. -/
lemma dynamicHeaderTailLen_eq_split :
    dynamicHeaderTailLen = dynamicHeaderCodeLenLen + 2 * dynamicHeaderCodeLenSyms.length := by
  simp [dynamicHeaderTailLen, dynamicHeaderCodeLenLen, dynamicHeaderCodeLenSyms_length]

/-- Records the reversed two-bit code used for code-length symbol `5`. -/
lemma dynamicCodeLenSymRevBits_five : dynamicCodeLenSymRevBits 5 = 0 := by
  simp [dynamicCodeLenSymRevBits]

/-- Records the reversed two-bit code used for code-length symbol `7`. -/
lemma dynamicCodeLenSymRevBits_seven : dynamicCodeLenSymRevBits 7 = 2 := by
  simp [dynamicCodeLenSymRevBits]

/-- Records the reversed two-bit code used for code-length symbol `8`. -/
lemma dynamicCodeLenSymRevBits_eight : dynamicCodeLenSymRevBits 8 = 1 := by
  simp [dynamicCodeLenSymRevBits]

/-- Records the reversed two-bit code used for code-length symbol `9`. -/
lemma dynamicCodeLenSymRevBits_nine : dynamicCodeLenSymRevBits 9 = 3 := by
  simp [dynamicCodeLenSymRevBits]

/-- Shows that the fixed code-length lengths decode to the intended 2-bit helper Huffman table. -/
lemma mkHuffman_dynamicCodeLenLengths :
    mkHuffman dynamicCodeLenLengths = some dynamicCodeLenHuffman := by
  native_decide

/-- Fixes the size of the synthetic fixed distance row used by the dynamic stream. -/
lemma fixedDistRow5_size : fixedDistRow5.size = 1 <<< 5 := by
  simp [fixedDistRow5]

/-- Identifies the concrete entry selected in the synthetic distance row after bit reversal. -/
lemma fixedDistRow5_get (code : Nat) (hcode : code < 32) :
    fixedDistRow5[reverseBits code 5]'(by
      simpa [fixedDistRow5_size, Nat.shiftLeft_eq] using reverseBits_lt code 5) =
      some code := by
  have hrev : reverseBits (reverseBits code 5) 5 = code := by
    exact reverseBits_reverseBits code 5 (by simpa [Nat.shiftLeft_eq] using hcode)
  simp [fixedDistRow5, Array.getElem_ofFn, hrev]

/-- Shows that the dynamic stream reuses the fixed literal/length decoder table exactly. -/
lemma mkHuffman_dynamicLitLenLengths :
    mkHuffman dynamicLitLenLengths = some fixedLitLenHuffman := by
  native_decide

/-- Shows that the dynamic stream reuses the fixed distance decoder table exactly. -/
lemma mkHuffman_dynamicDistLengths :
    mkHuffman dynamicDistLengths = some fixedDistHuffman := by
  native_decide

/-- Confirms that replaying the header order reconstructs the intended code-length-length array. -/
lemma dynamicCodeLenLengthsFilled_eq :
    dynamicCodeLenLengthsFilled = dynamicCodeLenLengths := by
  native_decide

/-- Splits the tail bit payload into the code-length lengths and the encoded symbol stream. -/
lemma dynamicHeaderTailBits_eq_split :
    dynamicHeaderTailBits =
      dynamicHeaderCodeLenLenBits |||
        (dynamicCodeLenSymBits dynamicHeaderCodeLenSyms <<< dynamicHeaderCodeLenLen) := by
  native_decide

/-- Rewrites the concrete table writer into one bulk `writeBits`, which later reader proofs consume. -/
lemma writeDynamicFixedTables_eq_writeBits :
    let bw0 := BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 2 2
    let bw3 := bw2.writeBits 31 5
    let bw4 := bw3.writeBits 31 5
    let bw5 := bw4.writeBits 6 4
    writeDynamicFixedTables bw5 =
      BitWriter.writeBits bw5 dynamicHeaderTailBits dynamicHeaderTailLen := by
  native_decide

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 2000 in
/-- Collapses the runtime dynamic encoder into a single header-plus-fixed-payload `writeBits` form. -/
lemma deflateDynamicFast_eq_writeBits (raw : ByteArray) :
    let payloadBits := fixedLitBitsEob raw.data 0
    deflateDynamicFast raw =
      (BitWriter.writeBits BitWriter.empty
        (5 ||| (dynamicHeaderTableBits <<< 3) ||| (payloadBits.1 <<< (3 + dynamicHeaderTableLen)))
        (3 + dynamicHeaderTableLen + payloadBits.2)).flush := by
  let payloadBits := fixedLitBitsEob raw.data 0
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 2 2
  let bw3 := bw2.writeBits 31 5
  let bw4 := bw3.writeBits 31 5
  let bw5 := bw4.writeBits 6 4
  let bw6 := writeDynamicFixedTables bw5
  let bw7 := deflateFixedAuxFast raw.data 0 bw6
  let eob := fixedLitLenCode 256
  let bw8 := BitWriter.writeBits bw7 (reverseBits eob.1 eob.2) eob.2
  have heobFast :
      fixedLitLenRevCodeFast 256 = (reverseBits eob.1 eob.2, eob.2) := by
    simpa [eob] using fixedLitLenRevCodeFast_eq 256 (by decide)
  have hbw6 :
      bw6 = BitWriter.writeBits bw2 dynamicHeaderTableBits dynamicHeaderTableLen := by
    native_decide
  have hpayload :
      BitWriter.writeBits bw6 payloadBits.1 payloadBits.2 = bw8 := by
    have hbits :=
      fixedLitBitsEob_writeBits (data := raw.data) (i := 0) (bw := bw6)
    have hb8 : bw8 =
        BitWriter.writeBits
          (deflateFixedAux raw.data 0 bw6)
          (reverseBits eob.1 eob.2) eob.2 := by
      simp [bw8, bw7, eob, deflateFixedAuxFast_eq_spec]
    simpa [payloadBits, eob] using hbits.trans hb8.symm
  have hconcat1 :
      BitWriter.writeBits bw0 (5 ||| (dynamicHeaderTableBits <<< 3)) (3 + dynamicHeaderTableLen) =
        BitWriter.writeBits bw2 dynamicHeaderTableBits dynamicHeaderTableLen := by
    native_decide
  have hpayloadBitsLt : 5 ||| (dynamicHeaderTableBits <<< 3) < 2 ^ (3 + dynamicHeaderTableLen) := by
    native_decide
  have hconcat2 :
      BitWriter.writeBits bw0
        (5 ||| (dynamicHeaderTableBits <<< 3) ||| (payloadBits.1 <<< (3 + dynamicHeaderTableLen)))
        (3 + dynamicHeaderTableLen + payloadBits.2) =
      BitWriter.writeBits
        (BitWriter.writeBits bw0 (5 ||| (dynamicHeaderTableBits <<< 3)) (3 + dynamicHeaderTableLen))
        payloadBits.1 payloadBits.2 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (writeBits_concat bw0
        (5 ||| (dynamicHeaderTableBits <<< 3)) payloadBits.1
        (3 + dynamicHeaderTableLen) payloadBits.2 hpayloadBitsLt)
  have hpayloadFlush :
      bw8.flush = (BitWriter.writeBits bw6 payloadBits.1 payloadBits.2).flush := by
    simpa using congrArg BitWriter.flush hpayload.symm
  unfold deflateDynamicFast
  have hmain :
      ((deflateFixedAuxFast raw.data 0 (writeDynamicFixedTables bw5)).writeBits
        (fixedLitLenRevCodeFast 256).1 (fixedLitLenRevCodeFast 256).2).flush =
      (BitWriter.writeBits bw0
        (5 ||| (dynamicHeaderTableBits <<< 3) ||| (payloadBits.1 <<< (3 + dynamicHeaderTableLen)))
        (3 + dynamicHeaderTableLen + payloadBits.2)).flush := by
    calc
      ((deflateFixedAuxFast raw.data 0 (writeDynamicFixedTables bw5)).writeBits
          (fixedLitLenRevCodeFast 256).1 (fixedLitLenRevCodeFast 256).2).flush
          = bw8.flush := by
            simp [bw8, bw7, bw6, eob, heobFast]
      _ =
        (BitWriter.writeBits bw6 payloadBits.1 payloadBits.2).flush := hpayloadFlush
      _ =
        (BitWriter.writeBits (BitWriter.writeBits bw2 dynamicHeaderTableBits dynamicHeaderTableLen)
          payloadBits.1 payloadBits.2).flush := by
            simp [hbw6]
      _ =
        (BitWriter.writeBits
          (BitWriter.writeBits bw0 (5 ||| (dynamicHeaderTableBits <<< 3)) (3 + dynamicHeaderTableLen))
          payloadBits.1 payloadBits.2).flush := by
            simp [hconcat1]
      _ =
        (BitWriter.writeBits bw0
          (5 ||| (dynamicHeaderTableBits <<< 3) ||| (payloadBits.1 <<< (3 + dynamicHeaderTableLen)))
          (3 + dynamicHeaderTableLen + payloadBits.2)).flush := by
            simp [hconcat2]
  simpa [bw8, bw7, bw6, bw5, bw4, bw3, bw2, bw1, bw0, eob, writeBitsFast_eq_writeBits] using hmain

end Png

end Bitmaps
