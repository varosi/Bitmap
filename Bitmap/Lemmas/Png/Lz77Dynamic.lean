import Bitmap.Lemmas.Png.DynamicEncoderPayload
import Bitmap.Lemmas.Png.Lz77

namespace Bitmaps

namespace Lemmas

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Proof-facing bit width for one generated dynamic LZ77 payload token.
It mirrors the literal/length code, length extra bits, distance code, and
distance extra bits emitted by `writeDynamicPayloadLz77`. -/
def dynamicPayloadLz77TokenBitLen
    (litLenCodes distCodes : Array (Nat × Nat)) : Png.Lz77Token → Nat
  | .literal b => litLenCodes[b.toNat]!.2
  | .match len distance =>
      let (sym, _extraBits, extraLen) := Png.deflateLengthInfo len
      match Png.deflateDistanceInfo? distance with
      | some (distSym, _distExtraBits, distExtraLen) =>
          litLenCodes[sym]!.2 + extraLen + distCodes[distSym]!.2 + distExtraLen
      | none =>
          litLenCodes[sym]!.2 + extraLen + distCodes[0]!.2

/-- Proof-facing packed bits for one generated dynamic LZ77 payload token.
The low bits are the literal/length code, followed by any match extra bits
and the distance-code fragment. -/
def dynamicPayloadLz77TokenBits
    (litLenCodes distCodes : Array (Nat × Nat)) : Png.Lz77Token → Nat
  | .literal b => litLenCodes[b.toNat]!.1
  | .match len distance =>
      let (sym, extraBits, extraLen) := Png.deflateLengthInfo len
      let litBits := litLenCodes[sym]!.1
      let litLen := litLenCodes[sym]!.2
      match Png.deflateDistanceInfo? distance with
      | some (distSym, distExtraBits, _distExtraLen) =>
          let distBits := distCodes[distSym]!.1
          let distLen := distCodes[distSym]!.2
          litBits ||| (extraBits <<< litLen) |||
            (distBits <<< (litLen + extraLen)) |||
            (distExtraBits <<< (litLen + extraLen + distLen))
      | none =>
          let distBits := distCodes[0]!.1
          litBits ||| (extraBits <<< litLen) |||
            (distBits <<< (litLen + extraLen))

/-- Proof-facing bit width of the generated dynamic LZ77 payload terminator. -/
def dynamicPayloadLz77EobBitLen (litLenCodes : Array (Nat × Nat)) : Nat :=
  litLenCodes[256]!.2

/-- Proof-facing packed bits of the generated dynamic LZ77 payload terminator. -/
def dynamicPayloadLz77EobBits (litLenCodes : Array (Nat × Nat)) : Nat :=
  litLenCodes[256]!.1

/-- Packed little-endian stream for generated dynamic LZ77 payload tokens plus
the final EOB marker. Later trace proofs replay this exact stream. -/
def dynamicPayloadLz77StreamBits
    (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.Lz77Token → Nat
  | [] => dynamicPayloadLz77EobBits litLenCodes
  | token :: tokens =>
      dynamicPayloadLz77TokenBits litLenCodes distCodes token |||
        (dynamicPayloadLz77StreamBits litLenCodes distCodes tokens <<<
          dynamicPayloadLz77TokenBitLen litLenCodes distCodes token)

/-- Total bit width of the generated dynamic LZ77 payload token stream plus
the EOB marker. -/
def dynamicPayloadLz77StreamLen
    (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.Lz77Token → Nat
  | [] => dynamicPayloadLz77EobBitLen litLenCodes
  | token :: tokens =>
      dynamicPayloadLz77TokenBitLen litLenCodes distCodes token +
        dynamicPayloadLz77StreamLen litLenCodes distCodes tokens

/-- Proof-facing writer for one generated dynamic LZ77 payload token. It is a
single-token view of the runtime loop, giving payload proofs an induction
step that matches `writeDynamicPayloadLz77`. -/
def writeDynamicPayloadLz77Token
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat)) :
    Png.Lz77Token → Png.BitWriter
  | .literal b =>
      bw.writeRevCode litLenCodes b.toNat
  | .match len distance =>
      let (sym, extraBits, extraLen) := Png.deflateLengthInfo len
      let bw := bw.writeRevCode litLenCodes sym
      let bw := bw.writeBitsFast extraBits extraLen
      match Png.deflateDistanceInfo? distance with
      | some (distSym, distExtraBits, distExtraLen) =>
          let bw := bw.writeRevCode distCodes distSym
          bw.writeBitsFast distExtraBits distExtraLen
      | none =>
          bw.writeRevCode distCodes 0

/-- A literal LZ77 payload write is exactly a write of the packed
literal/length code. This removes the `writeRevCode` wrapper in the literal
case of dynamic LZ77 stream replay. -/
lemma writeDynamicPayloadLz77Token_literal_eq_writeBits
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat))
    (b : UInt8) :
    writeDynamicPayloadLz77Token bw litLenCodes distCodes
        (Png.Lz77Token.literal b) =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77TokenBits litLenCodes distCodes
          (Png.Lz77Token.literal b))
        (dynamicPayloadLz77TokenBitLen litLenCodes distCodes
          (Png.Lz77Token.literal b)) := by
  simp [writeDynamicPayloadLz77Token, dynamicPayloadLz77TokenBits,
    dynamicPayloadLz77TokenBitLen, Png.BitWriter.writeRevCode,
    Png.writeBitsFast_eq_writeBits]

/-- An LZ77 dynamic EOB payload write is exactly a write of the packed EOB
code. This is the terminal writer bridge for dynamic LZ77 payload replay. -/
lemma writeDynamicPayloadLz77Eob_eq_writeBits
    (bw : Png.BitWriter) (litLenCodes : Array (Nat × Nat)) :
    bw.writeRevCode litLenCodes 256 =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77EobBits litLenCodes)
        (dynamicPayloadLz77EobBitLen litLenCodes) := by
  simp [dynamicPayloadLz77EobBits, dynamicPayloadLz77EobBitLen,
    Png.BitWriter.writeRevCode, Png.writeBitsFast_eq_writeBits]

/-- A valid LZ77 match payload write is exactly a write of the packed match
bits. This is the arbitrary-distance counterpart of the old distance-1
dynamic payload bridge. -/
lemma writeDynamicPayloadLz77Token_match_some_eq_writeBits
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat))
    {len distance sym extraBits extraLen distSym distExtraBits distExtraLen : Nat}
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (hlitBits : litLenCodes[sym]!.1 < 2 ^ litLenCodes[sym]!.2)
    (hextraBits : extraBits < 2 ^ extraLen)
    (hdistBits : distCodes[distSym]!.1 < 2 ^ distCodes[distSym]!.2)
    (hdistExtraBits : distExtraBits < 2 ^ distExtraLen) :
    writeDynamicPayloadLz77Token bw litLenCodes distCodes
        (Png.Lz77Token.match len distance) =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77TokenBits litLenCodes distCodes
          (Png.Lz77Token.match len distance))
        (dynamicPayloadLz77TokenBitLen litLenCodes distCodes
          (Png.Lz77Token.match len distance)) := by
  let litBits := litLenCodes[sym]!.1
  let litLen := litLenCodes[sym]!.2
  let distBits := distCodes[distSym]!.1
  let distLen := distCodes[distSym]!.2
  let lenPrefixBits := litBits ||| (extraBits <<< litLen)
  let lenPrefixLen := litLen + extraLen
  let distPrefixBits := lenPrefixBits ||| (distBits <<< lenPrefixLen)
  let distPrefixLen := lenPrefixLen + distLen
  have hextraShift :
      extraBits <<< litLen < 2 ^ lenPrefixLen := by
    simpa [lenPrefixLen, litLen, Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right hextraBits (Nat.two_pow_pos litLen)
  have hlitWide : litBits < 2 ^ lenPrefixLen := by
    exact lt_of_lt_of_le hlitBits
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (by simp [lenPrefixLen, litLen]))
  have hlenPrefixBits : lenPrefixBits < 2 ^ lenPrefixLen := by
    exact Nat.or_lt_two_pow hlitWide hextraShift
  have hdistShift :
      distBits <<< lenPrefixLen < 2 ^ distPrefixLen := by
    simpa [distPrefixLen, lenPrefixLen, distLen, Nat.shiftLeft_eq,
      Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right hdistBits (Nat.two_pow_pos lenPrefixLen)
  have hlenPrefixWide : lenPrefixBits < 2 ^ distPrefixLen := by
    exact lt_of_lt_of_le hlenPrefixBits
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (by simp [distPrefixLen]))
  have hdistPrefixBits : distPrefixBits < 2 ^ distPrefixLen := by
    exact Nat.or_lt_two_pow hlenPrefixWide hdistShift
  have hdistExtraShift :
      distExtraBits <<< distPrefixLen <
        2 ^ (distPrefixLen + distExtraLen) := by
    simpa [distPrefixLen, Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right hdistExtraBits
        (Nat.two_pow_pos distPrefixLen)
  have hdistPrefixWide :
      distPrefixBits < 2 ^ (distPrefixLen + distExtraLen) := by
    exact lt_of_lt_of_le hdistPrefixBits
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (Nat.le_add_right distPrefixLen distExtraLen))
  have hconcatLit :
      Png.BitWriter.writeBits bw lenPrefixBits lenPrefixLen =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw litBits litLen)
          extraBits extraLen := by
    simpa [lenPrefixBits, lenPrefixLen] using
      Png.writeBits_concat bw litBits extraBits litLen extraLen hlitBits
  have hconcatDist :
      Png.BitWriter.writeBits bw distPrefixBits distPrefixLen =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw lenPrefixBits lenPrefixLen)
          distBits distLen := by
    simpa [distPrefixBits, distPrefixLen, lenPrefixLen] using
      Png.writeBits_concat bw lenPrefixBits distBits lenPrefixLen distLen
        hlenPrefixBits
  have hconcatDistExtra :
      Png.BitWriter.writeBits bw
          (distPrefixBits ||| (distExtraBits <<< distPrefixLen))
          (distPrefixLen + distExtraLen) =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw distPrefixBits distPrefixLen)
          distExtraBits distExtraLen := by
    exact Png.writeBits_concat bw distPrefixBits distExtraBits distPrefixLen
      distExtraLen hdistPrefixBits
  calc
    writeDynamicPayloadLz77Token bw litLenCodes distCodes
        (Png.Lz77Token.match len distance)
        =
      Png.BitWriter.writeBits
        (Png.BitWriter.writeBits
          (Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bw litBits litLen)
            extraBits extraLen)
          distBits distLen)
        distExtraBits distExtraLen := by
          simp [writeDynamicPayloadLz77Token, Png.BitWriter.writeRevCode,
            Png.writeBitsFast_eq_writeBits, hlenInfo, hdistInfo, litBits,
            litLen, distBits, distLen]
    _ =
      Png.BitWriter.writeBits
        (Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw lenPrefixBits lenPrefixLen)
          distBits distLen)
        distExtraBits distExtraLen := by
          rw [hconcatLit]
    _ =
      Png.BitWriter.writeBits
        (Png.BitWriter.writeBits bw distPrefixBits distPrefixLen)
        distExtraBits distExtraLen := by
          rw [hconcatDist]
    _ =
      Png.BitWriter.writeBits bw
        (distPrefixBits ||| (distExtraBits <<< distPrefixLen))
        (distPrefixLen + distExtraLen) := by
          rw [hconcatDistExtra]
    _ =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77TokenBits litLenCodes distCodes
          (Png.Lz77Token.match len distance))
        (dynamicPayloadLz77TokenBitLen litLenCodes distCodes
          (Png.Lz77Token.match len distance)) := by
          have hpacked :
              litBits ||| (extraBits <<< litLen) |||
                  (distBits <<< (litLen + extraLen)) |||
                (distExtraBits <<< (litLen + extraLen + distLen)) =
              distPrefixBits ||| (distExtraBits <<< distPrefixLen) := by
            simp [distPrefixBits, lenPrefixBits, lenPrefixLen, distPrefixLen,
              litBits, litLen, distBits, distLen, Nat.or_assoc]
          simp [dynamicPayloadLz77TokenBits, dynamicPayloadLz77TokenBitLen,
            hlenInfo, hdistInfo, litBits, litLen, distBits, distLen,
            lenPrefixBits, lenPrefixLen, distPrefixBits, distPrefixLen,
            hpacked, Nat.add_assoc]

/-- Packed dynamic LZ77 match bits fit in their advertised bit width whenever
the literal/length code, distance code, and both extra-bit fields do. -/
lemma dynamicPayloadLz77TokenBits_match_some_lt_codeSpace
    (litLenCodes distCodes : Array (Nat × Nat))
    {len distance sym extraBits extraLen distSym distExtraBits distExtraLen : Nat}
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (hlitBits : litLenCodes[sym]!.1 < 2 ^ litLenCodes[sym]!.2)
    (hextraBits : extraBits < 2 ^ extraLen)
    (hdistBits : distCodes[distSym]!.1 < 2 ^ distCodes[distSym]!.2)
    (hdistExtraBits : distExtraBits < 2 ^ distExtraLen) :
    dynamicPayloadLz77TokenBits litLenCodes distCodes
        (Png.Lz77Token.match len distance) <
      2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes
        (Png.Lz77Token.match len distance) := by
  let litBits := litLenCodes[sym]!.1
  let litLen := litLenCodes[sym]!.2
  let distBits := distCodes[distSym]!.1
  let distLen := distCodes[distSym]!.2
  let lenPrefixBits := litBits ||| (extraBits <<< litLen)
  let lenPrefixLen := litLen + extraLen
  let distPrefixBits := lenPrefixBits ||| (distBits <<< lenPrefixLen)
  let distPrefixLen := lenPrefixLen + distLen
  have hextraShift :
      extraBits <<< litLen < 2 ^ lenPrefixLen := by
    simpa [lenPrefixLen, litLen, Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right hextraBits (Nat.two_pow_pos litLen)
  have hlitWide : litBits < 2 ^ lenPrefixLen := by
    exact lt_of_lt_of_le hlitBits
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (by simp [lenPrefixLen, litLen]))
  have hlenPrefixBits : lenPrefixBits < 2 ^ lenPrefixLen := by
    exact Nat.or_lt_two_pow hlitWide hextraShift
  have hdistShift :
      distBits <<< lenPrefixLen < 2 ^ distPrefixLen := by
    simpa [distPrefixLen, lenPrefixLen, distLen, Nat.shiftLeft_eq,
      Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right hdistBits (Nat.two_pow_pos lenPrefixLen)
  have hlenPrefixWide : lenPrefixBits < 2 ^ distPrefixLen := by
    exact lt_of_lt_of_le hlenPrefixBits
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (by simp [distPrefixLen]))
  have hdistPrefixBits : distPrefixBits < 2 ^ distPrefixLen := by
    exact Nat.or_lt_two_pow hlenPrefixWide hdistShift
  have hdistExtraShift :
      distExtraBits <<< distPrefixLen <
        2 ^ (distPrefixLen + distExtraLen) := by
    simpa [distPrefixLen, Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right hdistExtraBits
        (Nat.two_pow_pos distPrefixLen)
  have hdistPrefixWide :
      distPrefixBits < 2 ^ (distPrefixLen + distExtraLen) := by
    exact lt_of_lt_of_le hdistPrefixBits
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (Nat.le_add_right distPrefixLen distExtraLen))
  have hpacked :
      litBits ||| (extraBits <<< litLen) |||
          (distBits <<< (litLen + extraLen)) |||
        (distExtraBits <<< (litLen + extraLen + distLen)) =
      distPrefixBits ||| (distExtraBits <<< distPrefixLen) := by
    simp [distPrefixBits, lenPrefixBits, lenPrefixLen, distPrefixLen,
      litBits, litLen, distBits, distLen, Nat.or_assoc]
  have hbits :
      distPrefixBits ||| (distExtraBits <<< distPrefixLen) <
        2 ^ (distPrefixLen + distExtraLen) :=
    Nat.or_lt_two_pow hdistPrefixWide hdistExtraShift
  simpa [dynamicPayloadLz77TokenBits, dynamicPayloadLz77TokenBitLen,
    hlenInfo, hdistInfo, litBits, litLen, distBits, distLen,
    lenPrefixBits, lenPrefixLen, distPrefixBits, distPrefixLen,
    hpacked, Nat.add_assoc] using hbits

/-- The v1 generated LZ77 dynamic distance table advertises all 30 DEFLATE
distance symbols. This keeps payload proofs independent of distance frequency
shape. -/
lemma generatedDynamicDistLengthsLz77_size (freqs : Array Nat) :
    (Png.generatedDynamicDistLengthsLz77 freqs).size = 30 := by
  simp [Png.generatedDynamicDistLengthsLz77]

/-- Every advertised v1 LZ77 dynamic distance symbol has concrete width five.
This is the code-length lookup used by arbitrary-distance payload matches. -/
lemma generatedDynamicDistLengthsLz77_get!_eq_five
    (freqs : Array Nat) (sym : Nat)
    (hsym : sym < (Png.generatedDynamicDistLengthsLz77 freqs).size) :
    (Png.generatedDynamicDistLengthsLz77 freqs)[sym]! = 5 := by
  have hsymRep : sym < (Array.replicate 30 5).size := by
    simpa [Png.generatedDynamicDistLengthsLz77] using hsym
  simpa [Png.generatedDynamicDistLengthsLz77] using
    (by
      rw [getElem!_pos (Array.replicate 30 5) sym hsymRep]
      simp)

/-- Canonical code generation preserves the v1 LZ77 distance symbol width.
Payload writer proofs use this after `deflateDistanceInfo?` bounds the symbol. -/
lemma generatedDynamicDistCodesLz77_len_eq_five
    (freqs : Array Nat) (sym : Nat)
    (hsym : sym < (Png.generatedDynamicDistLengthsLz77 freqs).size) :
    (Png.canonicalRevCodesFromLengths
      (Png.generatedDynamicDistLengthsLz77 freqs))[sym]!.2 = 5 := by
  let lengths := Png.generatedDynamicDistLengthsLz77 freqs
  have hpos : 0 < lengths[sym]! := by
    have hlen : lengths[sym]! = 5 := by
      simpa [lengths] using
        generatedDynamicDistLengthsLz77_get!_eq_five freqs sym hsym
    omega
  rw [canonicalRevCodesFromLengths_get!_snd_of_pos
    lengths sym hsym hpos]
  exact generatedDynamicDistLengthsLz77_get!_eq_five freqs sym hsym

/-- Generated LZ77 distance-code bit patterns fit in the advertised five-bit
row. This is the distance-symbol code-space bound for match writer replay. -/
lemma generatedDynamicDistCodesLz77_bits_lt_codeSpace
    (freqs : Array Nat) (sym : Nat)
    (hsym : sym < (Png.generatedDynamicDistLengthsLz77 freqs).size) :
    (Png.canonicalRevCodesFromLengths
      (Png.generatedDynamicDistLengthsLz77 freqs))[sym]!.1 < 2 ^ 5 := by
  let lengths := Png.generatedDynamicDistLengthsLz77 freqs
  have hpos : 0 < lengths[sym]! := by
    have hlen : lengths[sym]! = 5 := by
      simpa [lengths] using
        generatedDynamicDistLengthsLz77_get!_eq_five freqs sym hsym
    omega
  have hbits :
      (Png.canonicalRevCodesFromLengths lengths)[sym]!.1 <
        2 ^ lengths[sym]! :=
    canonicalRevCodesFromLengths_get!_fst_lt_pow_of_pos
      lengths sym hsym hpos
  have hlen := generatedDynamicDistLengthsLz77_get!_eq_five freqs sym hsym
  simpa [lengths, hlen] using hbits

/-- Canonical reversed-code bits fit in the code width stored beside them
whenever the source length table marks the symbol as present. -/
lemma canonicalRevCodesFromLengths_get!_fst_lt_pow_snd_of_pos
    (lengths : Array Nat) (sym : Nat)
    (hsym : sym < lengths.size)
    (hpos : 0 < lengths[sym]!) :
    (Png.canonicalRevCodesFromLengths lengths)[sym]!.1 <
      2 ^ (Png.canonicalRevCodesFromLengths lengths)[sym]!.2 := by
  have hbits :=
    canonicalRevCodesFromLengths_get!_fst_lt_pow_of_pos
      lengths sym hsym hpos
  have hlen :=
    canonicalRevCodesFromLengths_get!_snd_of_pos lengths sym hsym hpos
  simpa [hlen] using hbits

/-- LZ77 literal/length frequency scanning preserves the frequency table size.
Generated-code proofs use this to recover the 286-symbol alphabet shape. -/
lemma litLenSymbolFreqsLz77Aux_size
    (tokens : Array Png.Lz77Token) (i : Nat) (freqs : Array Nat) :
    (Png.litLenSymbolFreqsLz77Aux tokens i freqs).size = freqs.size := by
  rw [Png.litLenSymbolFreqsLz77Aux.eq_1]
  by_cases h : i < tokens.size
  · cases htok : tokens[i] with
    | literal b =>
        have hrec :=
          litLenSymbolFreqsLz77Aux_size tokens (i + 1)
            (Png.incrementNatAt freqs b.toNat)
        simpa [h, htok] using hrec
    | «match» len distance =>
        have hrec :=
          litLenSymbolFreqsLz77Aux_size tokens (i + 1)
            (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1)
        simpa [h, htok] using hrec
  · simp [h]
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- LZ77 literal/length frequency collection has the DEFLATE literal/length
alphabet size. The final EOB increment preserves the 286-entry table. -/
lemma litLenSymbolFreqsLz77_size (tokens : Array Png.Lz77Token) :
    (Png.litLenSymbolFreqsLz77 tokens).size = 286 := by
  simp [Png.litLenSymbolFreqsLz77, litLenSymbolFreqsLz77Aux_size]

/-- The generated LZ77 literal/length frequency table always contains a
positive EOB count. Dynamic payload proofs need this for the terminal code. -/
lemma litLenSymbolFreqsLz77_eob_pos (tokens : Array Png.Lz77Token) :
    0 < (Png.litLenSymbolFreqsLz77 tokens)[256]! := by
  have hsize :
      (Png.litLenSymbolFreqsLz77Aux tokens 0 (Array.replicate 286 0)).size =
        286 := by
    simpa using
      (litLenSymbolFreqsLz77Aux_size tokens 0 (Array.replicate 286 0))
  have hidx :
      256 <
        (Png.litLenSymbolFreqsLz77Aux tokens 0
          (Array.replicate 286 0)).size := by
    omega
  simpa [Png.litLenSymbolFreqsLz77] using
    incrementNatAt_get!_pos
      (Png.litLenSymbolFreqsLz77Aux tokens 0 (Array.replicate 286 0)) 256 hidx

/-- LZ77 literal/length scanning preserves an already-positive frequency
bucket. This is the recursive invariant behind token-symbol availability. -/
lemma litLenSymbolFreqsLz77Aux_pos_of_pos
    (tokens : Array Png.Lz77Token) (i : Nat) (freqs : Array Nat) (sym : Nat)
    (hpos : 0 < freqs[sym]!) :
    0 < (Png.litLenSymbolFreqsLz77Aux tokens i freqs)[sym]! := by
  rw [Png.litLenSymbolFreqsLz77Aux.eq_1]
  by_cases h : i < tokens.size
  · cases htok : tokens[i] with
    | literal b =>
        have hinc :
            0 < (Png.incrementNatAt freqs b.toNat)[sym]! :=
          incrementNatAt_get!_pos_of_pos freqs b.toNat sym hpos
        have hrec :=
          litLenSymbolFreqsLz77Aux_pos_of_pos tokens (i + 1)
            (Png.incrementNatAt freqs b.toNat) sym hinc
        simpa [h, htok] using hrec
    | «match» len distance =>
        have hinc :
            0 < (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1)[sym]! :=
          incrementNatAt_get!_pos_of_pos freqs (Png.deflateLengthInfo len).1 sym hpos
        have hrec :=
          litLenSymbolFreqsLz77Aux_pos_of_pos tokens (i + 1)
            (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1) sym hinc
        simpa [h, htok] using hrec
  · simpa [h] using hpos
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- The current literal token makes its literal/length symbol positive in the
remaining LZ77 frequency scan. -/
lemma litLenSymbolFreqsLz77Aux_literal_pos_of_current
    (tokens : Array Png.Lz77Token) (i : Nat) (freqs : Array Nat) (b : UInt8)
    (htarget : i < tokens.size)
    (ht : tokens[i]'htarget = Png.Lz77Token.literal b)
    (hidx : b.toNat < freqs.size) :
    0 < (Png.litLenSymbolFreqsLz77Aux tokens i freqs)[b.toNat]! := by
  rw [Png.litLenSymbolFreqsLz77Aux.eq_1]
  have hinc :
      0 < (Png.incrementNatAt freqs b.toNat)[b.toNat]! :=
    incrementNatAt_get!_pos freqs b.toNat hidx
  have hrec :=
    litLenSymbolFreqsLz77Aux_pos_of_pos tokens (i + 1)
      (Png.incrementNatAt freqs b.toNat) b.toNat hinc
  simpa [htarget, ht] using hrec

/-- The current match token makes its match-length symbol positive in the
remaining LZ77 frequency scan. -/
lemma litLenSymbolFreqsLz77Aux_match_pos_of_current
    (tokens : Array Png.Lz77Token) (i : Nat) (freqs : Array Nat)
    (len distance : Nat)
    (htarget : i < tokens.size)
    (ht : tokens[i]'htarget = Png.Lz77Token.match len distance)
    (hidx : (Png.deflateLengthInfo len).1 < freqs.size) :
    0 <
      (Png.litLenSymbolFreqsLz77Aux tokens i freqs)[(Png.deflateLengthInfo len).1]! := by
  rw [Png.litLenSymbolFreqsLz77Aux.eq_1]
  have hinc :
      0 <
        (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1)[(Png.deflateLengthInfo len).1]! :=
    incrementNatAt_get!_pos freqs (Png.deflateLengthInfo len).1 hidx
  have hrec :=
    litLenSymbolFreqsLz77Aux_pos_of_pos tokens (i + 1)
      (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1)
      (Png.deflateLengthInfo len).1 hinc
  simpa [htarget, ht] using hrec

/-- Literal tokens later in the array receive positive generated LZ77
literal/length frequencies. This is the array-indexed literal availability
fact used by generated payload proofs. -/
lemma litLenSymbolFreqsLz77Aux_literal_pos_at
    (tokens : Array Png.Lz77Token) (i target : Nat) (freqs : Array Nat)
    (b : UInt8)
    (htarget : target < tokens.size)
    (hle : i ≤ target)
    (ht : tokens[target]'htarget = Png.Lz77Token.literal b)
    (hidx : b.toNat < freqs.size) :
    0 < (Png.litLenSymbolFreqsLz77Aux tokens i freqs)[b.toNat]! := by
  by_cases hit : i = target
  · subst target
    exact litLenSymbolFreqsLz77Aux_literal_pos_of_current
      tokens i freqs b htarget ht hidx
  · have hi : i < tokens.size := by omega
    rw [Png.litLenSymbolFreqsLz77Aux.eq_1]
    cases htok : tokens[i] with
    | literal b0 =>
        have hidx' : b.toNat < (Png.incrementNatAt freqs b0.toNat).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsLz77Aux_literal_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs b0.toNat) b htarget
            (by omega) ht hidx'
        simpa [hi, htok] using hrec
    | «match» len distance =>
        have hidx' :
            b.toNat <
              (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsLz77Aux_literal_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1) b htarget
            (by omega) ht hidx'
        simpa [hi, htok] using hrec
termination_by target - i
decreasing_by
  all_goals
    have hlt : i < target := by omega
    exact Nat.sub_lt_sub_left (k := i) (m := target) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Match tokens later in the array receive positive generated LZ77
literal/length frequencies for their length symbol. -/
lemma litLenSymbolFreqsLz77Aux_match_pos_at
    (tokens : Array Png.Lz77Token) (i target : Nat) (freqs : Array Nat)
    (len distance : Nat)
    (htarget : target < tokens.size)
    (hle : i ≤ target)
    (ht : tokens[target]'htarget = Png.Lz77Token.match len distance)
    (hidx : (Png.deflateLengthInfo len).1 < freqs.size) :
    0 <
      (Png.litLenSymbolFreqsLz77Aux tokens i freqs)[(Png.deflateLengthInfo len).1]! := by
  by_cases hit : i = target
  · subst target
    exact litLenSymbolFreqsLz77Aux_match_pos_of_current
      tokens i freqs len distance htarget ht hidx
  · have hi : i < tokens.size := by omega
    rw [Png.litLenSymbolFreqsLz77Aux.eq_1]
    cases htok : tokens[i] with
    | literal b0 =>
        have hidx' :
            (Png.deflateLengthInfo len).1 <
              (Png.incrementNatAt freqs b0.toNat).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsLz77Aux_match_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs b0.toNat) len distance htarget
            (by omega) ht hidx'
        simpa [hi, htok] using hrec
    | «match» len0 distance0 =>
        have hidx' :
            (Png.deflateLengthInfo len).1 <
              (Png.incrementNatAt freqs (Png.deflateLengthInfo len0).1).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsLz77Aux_match_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs (Png.deflateLengthInfo len0).1)
            len distance htarget (by omega) ht hidx'
        simpa [hi, htok] using hrec
termination_by target - i
decreasing_by
  all_goals
    have hlt : i < target := by omega
    exact Nat.sub_lt_sub_left (k := i) (m := target) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Literal tokens in the completed LZ77 frequency table have positive
frequencies, even after the final EOB increment. -/
lemma litLenSymbolFreqsLz77_literal_pos_at
    (tokens : Array Png.Lz77Token) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.Lz77Token.literal b) :
    0 < (Png.litLenSymbolFreqsLz77 tokens)[b.toNat]! := by
  have hidx : b.toNat < (Array.replicate 286 0).size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    simpa using (by omega : b.toNat < 286)
  have haux :
      0 <
        (Png.litLenSymbolFreqsLz77Aux tokens 0 (Array.replicate 286 0))[b.toNat]! :=
    litLenSymbolFreqsLz77Aux_literal_pos_at tokens 0 target
      (Array.replicate 286 0) b htarget (Nat.zero_le target) ht hidx
  simpa [Png.litLenSymbolFreqsLz77] using
    incrementNatAt_get!_pos_of_pos
      (Png.litLenSymbolFreqsLz77Aux tokens 0 (Array.replicate 286 0))
      256 b.toNat haux

/-- Match tokens in the completed LZ77 frequency table have positive
frequencies for their encoded match-length symbol. -/
lemma litLenSymbolFreqsLz77_match_pos_at
    (tokens : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    0 <
      (Png.litLenSymbolFreqsLz77 tokens)[(Png.deflateLengthInfo len).1]! := by
  have hidx : (Png.deflateLengthInfo len).1 < (Array.replicate 286 0).size := by
    have hsym := fixedLenMatchInfo_sym_lt_286 len hlen
    simpa [Png.deflateLengthInfo] using hsym
  have haux :
      0 <
        (Png.litLenSymbolFreqsLz77Aux tokens 0 (Array.replicate 286 0))[(Png.deflateLengthInfo len).1]! :=
    litLenSymbolFreqsLz77Aux_match_pos_at tokens 0 target
      (Array.replicate 286 0) len distance htarget (Nat.zero_le target) ht hidx
  simpa [Png.litLenSymbolFreqsLz77] using
    incrementNatAt_get!_pos_of_pos
      (Png.litLenSymbolFreqsLz77Aux tokens 0 (Array.replicate 286 0))
      256 (Png.deflateLengthInfo len).1 haux

/-- Generated literal/length tables mark an emitted LZ77 literal symbol as
present. This converts LZ77 frequency availability into code-length
availability. -/
lemma generatedDynamicLitLenLengthsLz77_literal_pos_at
    (tokens : Array Png.Lz77Token) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.Lz77Token.literal b) :
    0 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqsLz77 tokens))[b.toNat]! := by
  let freqs := Png.litLenSymbolFreqsLz77 tokens
  have hidx : b.toNat < freqs.size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize : freqs.size = 286 := by
      simpa [freqs] using litLenSymbolFreqsLz77_size tokens
    omega
  have hfreq : 0 < freqs[b.toNat]! := by
    simpa [freqs] using
      litLenSymbolFreqsLz77_literal_pos_at tokens target b htarget ht
  exact (generatedDynamicLitLenLengths_get!_pos_iff freqs b.toNat hidx).mpr hfreq

/-- Generated literal/length tables mark an emitted LZ77 match-length symbol
as present. This is the match-symbol counterpart of literal availability. -/
lemma generatedDynamicLitLenLengthsLz77_match_pos_at
    (tokens : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    0 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqsLz77 tokens))[(Png.deflateLengthInfo len).1]! := by
  let freqs := Png.litLenSymbolFreqsLz77 tokens
  have hidx : (Png.deflateLengthInfo len).1 < freqs.size := by
    have hsym := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize : freqs.size = 286 := by
      simpa [freqs] using litLenSymbolFreqsLz77_size tokens
    have hsym' : (Png.deflateLengthInfo len).1 < 286 := by
      simpa [Png.deflateLengthInfo] using hsym
    omega
  have hfreq : 0 < freqs[(Png.deflateLengthInfo len).1]! := by
    simpa [freqs] using
      litLenSymbolFreqsLz77_match_pos_at tokens target len distance
        htarget ht hlen
  exact
    (generatedDynamicLitLenLengths_get!_pos_iff
      freqs (Png.deflateLengthInfo len).1 hidx).mpr hfreq

/-- Generated dynamic LZ77 literal payload bits fit in their generated code
width. This supplies the literal branch of indexed payload replay. -/
lemma dynamicPayloadLz77TokenBits_generated_literal_lt_codeSpace_at
    (source : Array Png.Lz77Token) (target : Nat) (b : UInt8)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.literal b) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    dynamicPayloadLz77TokenBits litLenCodes distCodes
        (Png.Lz77Token.literal b) <
      2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes
        (Png.Lz77Token.literal b) := by
  intro litLenCodes distCodes
  let lengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  have hsym : b.toNat < lengths.size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size,
        litLenSymbolFreqsLz77_size]
    omega
  have hpos : 0 < lengths[b.toNat]! := by
    simpa [lengths] using
      generatedDynamicLitLenLengthsLz77_literal_pos_at source target b htarget ht
  have hbits :=
    canonicalRevCodesFromLengths_get!_fst_lt_pow_snd_of_pos
      lengths b.toNat hsym hpos
  simpa [dynamicPayloadLz77TokenBits, dynamicPayloadLz77TokenBitLen,
    litLenCodes, distCodes, lengths] using hbits

/-- Generated dynamic LZ77 match payload bits fit in their generated code
widths, including arbitrary valid distance symbols and distance extra bits. -/
lemma dynamicPayloadLz77TokenBits_generated_match_lt_codeSpace_at
    (source : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258)
    {distSym distExtraBits distExtraLen : Nat}
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen)) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    dynamicPayloadLz77TokenBits litLenCodes distCodes
        (Png.Lz77Token.match len distance) <
      2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes
        (Png.Lz77Token.match len distance) := by
  intro litLenCodes distCodes
  rcases hlenInfo : Png.deflateLengthInfo len with ⟨sym, extraBits, extraLen⟩
  have hlenSpec :=
    Png.deflateLengthInfo_decodeLength_correct hlenInfo hlen.1 hlen.2
  rcases hlenSpec with
    ⟨hsymBounds, _hidxBase, _hidxExtra, _hextraLen, _hbase, hextraBits⟩
  let litLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  have hlitSym : sym < litLengths.size := by
    have hsize : litLengths.size = 286 := by
      simp [litLengths, generatedDynamicLitLenLengths_size,
        litLenSymbolFreqsLz77_size]
    omega
  have hlitPos : 0 < litLengths[sym]! := by
    have hpos :=
      generatedDynamicLitLenLengthsLz77_match_pos_at source target len distance
        htarget ht hlen
    simpa [litLengths, hlenInfo] using hpos
  have hlitBits :
      litLenCodes[sym]!.1 < 2 ^ litLenCodes[sym]!.2 := by
    have hbits :=
      canonicalRevCodesFromLengths_get!_fst_lt_pow_snd_of_pos
        litLengths sym hlitSym hlitPos
    simpa [litLenCodes, litLengths] using hbits
  have hdistSpec :=
    Png.deflateDistanceInfo_decodeDistance_correct hdistInfo
  rcases hdistSpec with
    ⟨hdistSym, _hdistExtra, _hdistExtraLen, _hbase, hdistExtraBits⟩
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  have hdistSymLen : distSym < distLengths.size := by
    have hsize : distLengths.size = 30 := by
      simpa [distLengths] using
        generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
    have hbaseSize : Png.distBases.size = 30 := by decide
    omega
  have hdistPos : 0 < distLengths[distSym]! := by
    have hlen5 : distLengths[distSym]! = 5 := by
      simpa [distLengths] using
        generatedDynamicDistLengthsLz77_get!_eq_five
          (Png.distSymbolFreqsLz77 source) distSym hdistSymLen
    omega
  have hdistBits :
      distCodes[distSym]!.1 < 2 ^ distCodes[distSym]!.2 := by
    have hbits :=
      canonicalRevCodesFromLengths_get!_fst_lt_pow_snd_of_pos
        distLengths distSym hdistSymLen hdistPos
    simpa [distCodes, distLengths] using hbits
  exact dynamicPayloadLz77TokenBits_match_some_lt_codeSpace
    litLenCodes distCodes hlenInfo hdistInfo hlitBits hextraBits
    hdistBits hdistExtraBits

/-- Recursive list writer for generated dynamic LZ77 payload tokens. It
matches the runtime `for` loop while exposing structural recursion. -/
def writeDynamicPayloadLz77TokensList
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.Lz77Token → Png.BitWriter
  | [] => bw.writeRevCode litLenCodes 256
  | token :: tokens =>
      writeDynamicPayloadLz77TokensList
        (writeDynamicPayloadLz77Token bw litLenCodes distCodes token)
        litLenCodes distCodes tokens

/-- A recursive LZ77 payload-token list writes exactly its packed payload
stream once each token's writer and code-space bound are available. This
separates generic stream induction from generated Huffman-table facts. -/
lemma writeDynamicPayloadLz77TokensList_eq_writeBits
    (tokens : List Png.Lz77Token)
    (litLenCodes distCodes : Array (Nat × Nat))
    (hwrite :
      ∀ bw token, token ∈ tokens →
        writeDynamicPayloadLz77Token bw litLenCodes distCodes token =
          Png.BitWriter.writeBits bw
            (dynamicPayloadLz77TokenBits litLenCodes distCodes token)
            (dynamicPayloadLz77TokenBitLen litLenCodes distCodes token))
    (hbits :
      ∀ token, token ∈ tokens →
        dynamicPayloadLz77TokenBits litLenCodes distCodes token <
          2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes token)
    (bw : Png.BitWriter) :
    writeDynamicPayloadLz77TokensList bw litLenCodes distCodes tokens =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77StreamBits litLenCodes distCodes tokens)
        (dynamicPayloadLz77StreamLen litLenCodes distCodes tokens) := by
  induction tokens generalizing bw with
  | nil =>
      simpa [writeDynamicPayloadLz77TokensList,
        dynamicPayloadLz77StreamBits, dynamicPayloadLz77StreamLen] using
        writeDynamicPayloadLz77Eob_eq_writeBits bw litLenCodes
  | cons token tokens ih =>
      have htailWrite :
          ∀ bw token', token' ∈ tokens →
            writeDynamicPayloadLz77Token bw litLenCodes distCodes token' =
              Png.BitWriter.writeBits bw
                (dynamicPayloadLz77TokenBits litLenCodes distCodes token')
                (dynamicPayloadLz77TokenBitLen litLenCodes distCodes token') := by
        intro bw token' hmem
        exact hwrite bw token' (List.mem_cons_of_mem token hmem)
      have htailBits :
          ∀ token', token' ∈ tokens →
            dynamicPayloadLz77TokenBits litLenCodes distCodes token' <
              2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes token' := by
        intro token' hmem
        exact hbits token' (List.mem_cons_of_mem token hmem)
      have htokenWrite :
          writeDynamicPayloadLz77Token bw litLenCodes distCodes token =
            Png.BitWriter.writeBits bw
              (dynamicPayloadLz77TokenBits litLenCodes distCodes token)
              (dynamicPayloadLz77TokenBitLen litLenCodes distCodes token) :=
        hwrite bw token (by simp)
      have htokenBits :
          dynamicPayloadLz77TokenBits litLenCodes distCodes token <
            2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes token :=
        hbits token (by simp)
      have htail :=
        ih htailWrite htailBits
          (Png.BitWriter.writeBits bw
            (dynamicPayloadLz77TokenBits litLenCodes distCodes token)
            (dynamicPayloadLz77TokenBitLen litLenCodes distCodes token))
      have hconcat :
          Png.BitWriter.writeBits bw
              (dynamicPayloadLz77TokenBits litLenCodes distCodes token |||
                (dynamicPayloadLz77StreamBits litLenCodes distCodes tokens <<<
                  dynamicPayloadLz77TokenBitLen litLenCodes distCodes token))
              (dynamicPayloadLz77TokenBitLen litLenCodes distCodes token +
                dynamicPayloadLz77StreamLen litLenCodes distCodes tokens) =
            Png.BitWriter.writeBits
              (Png.BitWriter.writeBits bw
                (dynamicPayloadLz77TokenBits litLenCodes distCodes token)
                (dynamicPayloadLz77TokenBitLen litLenCodes distCodes token))
              (dynamicPayloadLz77StreamBits litLenCodes distCodes tokens)
              (dynamicPayloadLz77StreamLen litLenCodes distCodes tokens) :=
        Png.writeBits_concat bw
          (dynamicPayloadLz77TokenBits litLenCodes distCodes token)
          (dynamicPayloadLz77StreamBits litLenCodes distCodes tokens)
          (dynamicPayloadLz77TokenBitLen litLenCodes distCodes token)
          (dynamicPayloadLz77StreamLen litLenCodes distCodes tokens)
          htokenBits
      simp [writeDynamicPayloadLz77TokensList,
        dynamicPayloadLz77StreamBits, dynamicPayloadLz77StreamLen,
        htokenWrite, htail, hconcat]

/-- The list fold produced by Lean's `forIn` elaboration reduces to the
proof-facing recursive LZ77 payload list writer. -/
private lemma writeDynamicPayloadLz77TokensList_foldl
    (bw : Png.BitWriter) (tokens : List Png.Lz77Token)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    (List.foldl
        (fun acc token =>
          writeDynamicPayloadLz77Token acc litLenCodes distCodes token)
        bw tokens).writeRevCode litLenCodes 256 =
      writeDynamicPayloadLz77TokensList bw litLenCodes distCodes tokens := by
  induction tokens generalizing bw with
  | nil =>
      simp [writeDynamicPayloadLz77TokensList]
  | cons token tokens ih =>
      simp [writeDynamicPayloadLz77TokensList, ih]

/-- The runtime list `forIn` loop for LZ77 payload tokens reduces to the
proof-facing recursive list writer. -/
private lemma writeDynamicPayloadLz77TokensList_forIn
    (bw : Png.BitWriter) (tokens : List Png.Lz77Token)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    (Id.run <|
      forIn (m := Id) tokens bw fun token r =>
        pure (ForInStep.yield
          (writeDynamicPayloadLz77Token r litLenCodes distCodes token))).writeRevCode
      litLenCodes 256 =
      writeDynamicPayloadLz77TokensList bw litLenCodes distCodes tokens := by
  simpa using
    writeDynamicPayloadLz77TokensList_foldl bw tokens litLenCodes distCodes

/-- The runtime array LZ77 payload writer is the proof-facing list writer over
`Array.toList`. This bridges `writeDynamicPayloadLz77` to stream replay. -/
lemma writeDynamicPayloadLz77_eq_writeDynamicPayloadLz77TokensList
    (bw : Png.BitWriter) (tokens : Array Png.Lz77Token)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    Png.writeDynamicPayloadLz77 bw tokens litLenCodes distCodes =
      writeDynamicPayloadLz77TokensList bw litLenCodes distCodes tokens.toList := by
  cases tokens with
  | mk data =>
      induction data generalizing bw with
      | nil =>
          simp [Png.writeDynamicPayloadLz77, writeDynamicPayloadLz77TokensList]
      | cons token data ih =>
          cases token with
          | literal b =>
              simpa [Png.writeDynamicPayloadLz77,
                writeDynamicPayloadLz77TokensList,
                writeDynamicPayloadLz77Token] using
                ih (bw.writeRevCode litLenCodes b.toNat)
          | «match» len distance =>
              rcases hlenInfo : Png.deflateLengthInfo len with
                ⟨sym, extraBits, extraLen⟩
              cases hdistInfo : Png.deflateDistanceInfo? distance with
              | none =>
                  simpa [Png.writeDynamicPayloadLz77,
                    writeDynamicPayloadLz77TokensList,
                    writeDynamicPayloadLz77Token, hlenInfo, hdistInfo] using
                    ih
                      (((bw.writeRevCode litLenCodes sym).writeBits
                        extraBits extraLen).writeRevCode distCodes 0)
              | some distInfo =>
                  rcases distInfo with ⟨distSym, distExtraBits, distExtraLen⟩
                  simpa [Png.writeDynamicPayloadLz77,
                    writeDynamicPayloadLz77TokensList,
                    writeDynamicPayloadLz77Token, hlenInfo, hdistInfo] using
                    ih
                      ((((bw.writeRevCode litLenCodes sym).writeBits
                        extraBits extraLen).writeRevCode distCodes distSym).writeBits
                        distExtraBits distExtraLen)

/-- A token found in an LZ77 array's `toList` has a corresponding array index.
This lifts indexed validity and generated-code facts to list replay proofs. -/
lemma lz77Token_mem_toList_index
    {tokens : Array Png.Lz77Token} {token : Png.Lz77Token}
    (hmem : token ∈ tokens.toList) :
    ∃ target, ∃ htarget : target < tokens.size,
      tokens[target]'htarget = token := by
  rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
  have hidxArray : idx < tokens.size := by
    simpa using hidx
  have htoken : tokens[idx] = token := by
    simpa using hget
  exact ⟨idx, hidxArray, by simpa using htoken⟩

/-- Indexed token writer facts for an LZ77 source array lift to the packed
payload stream for `Array.toList`. Generated-table proofs can supply the
index facts without redoing the list induction. -/
lemma writeDynamicPayloadLz77TokensList_source_eq_writeBits_of_index
    (source : Array Png.Lz77Token)
    (litLenCodes distCodes : Array (Nat × Nat))
    (hwriteAt :
      ∀ bw target (htarget : target < source.size),
        writeDynamicPayloadLz77Token bw litLenCodes distCodes
            (source[target]'htarget) =
          Png.BitWriter.writeBits bw
            (dynamicPayloadLz77TokenBits litLenCodes distCodes
              (source[target]'htarget))
            (dynamicPayloadLz77TokenBitLen litLenCodes distCodes
              (source[target]'htarget)))
    (hbitsAt :
      ∀ target (htarget : target < source.size),
        dynamicPayloadLz77TokenBits litLenCodes distCodes
            (source[target]'htarget) <
          2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes
            (source[target]'htarget))
    (bw : Png.BitWriter) :
    writeDynamicPayloadLz77TokensList bw litLenCodes distCodes source.toList =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList)
        (dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList) := by
  exact
    writeDynamicPayloadLz77TokensList_eq_writeBits source.toList
      litLenCodes distCodes
      (fun bw token hmem => by
        rcases lz77Token_mem_toList_index (tokens := source) hmem with
          ⟨target, htarget, ht⟩
        simpa [ht] using hwriteAt bw target htarget)
      (fun token hmem => by
        rcases lz77Token_mem_toList_index (tokens := source) hmem with
          ⟨target, htarget, ht⟩
        simpa [ht] using hbitsAt target htarget)
      bw

/-- The runtime LZ77 dynamic payload writer emits the packed payload stream
when each source token has an indexed writer equality and code-space bound. -/
lemma writeDynamicPayloadLz77_eq_writeBits_of_index
    (source : Array Png.Lz77Token)
    (litLenCodes distCodes : Array (Nat × Nat))
    (hwriteAt :
      ∀ bw target (htarget : target < source.size),
        writeDynamicPayloadLz77Token bw litLenCodes distCodes
            (source[target]'htarget) =
          Png.BitWriter.writeBits bw
            (dynamicPayloadLz77TokenBits litLenCodes distCodes
              (source[target]'htarget))
            (dynamicPayloadLz77TokenBitLen litLenCodes distCodes
              (source[target]'htarget)))
    (hbitsAt :
      ∀ target (htarget : target < source.size),
        dynamicPayloadLz77TokenBits litLenCodes distCodes
            (source[target]'htarget) <
          2 ^ dynamicPayloadLz77TokenBitLen litLenCodes distCodes
            (source[target]'htarget))
    (bw : Png.BitWriter) :
    Png.writeDynamicPayloadLz77 bw source litLenCodes distCodes =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList)
        (dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList) := by
  calc
    Png.writeDynamicPayloadLz77 bw source litLenCodes distCodes =
        writeDynamicPayloadLz77TokensList bw litLenCodes distCodes source.toList := by
          exact writeDynamicPayloadLz77_eq_writeDynamicPayloadLz77TokensList
            bw source litLenCodes distCodes
    _ = Png.BitWriter.writeBits bw
        (dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList)
        (dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList) := by
          exact writeDynamicPayloadLz77TokensList_source_eq_writeBits_of_index
            source litLenCodes distCodes hwriteAt hbitsAt bw

/-- Generated LZ77 dynamic payloads write exactly their packed stream for any
source array whose match tokens are DEFLATE-length and distance encodable. -/
lemma writeDynamicPayloadLz77_source_generated_eq_writeBits
    (source : Array Png.Lz77Token)
    (hvalid :
      ∀ target (htarget : target < source.size),
        Png.Lz77TokenFixedValid (source[target]'htarget))
    (bw : Png.BitWriter) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    Png.writeDynamicPayloadLz77 bw source litLenCodes distCodes =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList)
        (dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList) := by
  intro litLenCodes distCodes
  refine writeDynamicPayloadLz77_eq_writeBits_of_index
    source litLenCodes distCodes ?_ ?_ bw
  · intro bw target htarget
    cases htok : source[target]'htarget with
    | literal b =>
        simpa [htok] using
          writeDynamicPayloadLz77Token_literal_eq_writeBits
            bw litLenCodes distCodes b
    | «match» len distance =>
        have hv := hvalid target htarget
        simp [Png.Lz77TokenFixedValid, htok] at hv
        rcases hv with
          ⟨hlenLo, hlenHi, distSym, distExtraBits, distExtraLen, hdistInfo⟩
        rcases hlenInfo : Png.deflateLengthInfo len with
          ⟨sym, extraBits, extraLen⟩
        have hlenSpec :=
          Png.deflateLengthInfo_decodeLength_correct hlenInfo hlenLo hlenHi
        rcases hlenSpec with
          ⟨hsymBounds, _hidxBase, _hidxExtra, _hextraLen, _hbase, hextraBits⟩
        let litLengths :=
          Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
        have hlitSym : sym < litLengths.size := by
          have hsize : litLengths.size = 286 := by
            simp [litLengths, generatedDynamicLitLenLengths_size,
              litLenSymbolFreqsLz77_size]
          omega
        have hlitPos : 0 < litLengths[sym]! := by
          have hpos :=
            generatedDynamicLitLenLengthsLz77_match_pos_at
              source target len distance htarget htok ⟨hlenLo, hlenHi⟩
          simpa [litLengths, hlenInfo] using hpos
        have hlitBits :
            litLenCodes[sym]!.1 < 2 ^ litLenCodes[sym]!.2 := by
          have hbits :=
            canonicalRevCodesFromLengths_get!_fst_lt_pow_snd_of_pos
              litLengths sym hlitSym hlitPos
          simpa [litLenCodes, litLengths] using hbits
        have hdistSpec :=
          Png.deflateDistanceInfo_decodeDistance_correct hdistInfo
        rcases hdistSpec with
          ⟨hdistSym, _hdistExtra, _hdistExtraLen, _hdistBase, hdistExtraBits⟩
        let distLengths :=
          Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
        have hdistSymLen : distSym < distLengths.size := by
          have hsize : distLengths.size = 30 := by
            simpa [distLengths] using
              generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
          have hbaseSize : Png.distBases.size = 30 := by decide
          omega
        have hdistPos : 0 < distLengths[distSym]! := by
          have hlen5 : distLengths[distSym]! = 5 := by
            simpa [distLengths] using
              generatedDynamicDistLengthsLz77_get!_eq_five
                (Png.distSymbolFreqsLz77 source) distSym hdistSymLen
          omega
        have hdistBits :
            distCodes[distSym]!.1 < 2 ^ distCodes[distSym]!.2 := by
          have hbits :=
            canonicalRevCodesFromLengths_get!_fst_lt_pow_snd_of_pos
              distLengths distSym hdistSymLen hdistPos
          simpa [distCodes, distLengths] using hbits
        simpa [htok] using
          writeDynamicPayloadLz77Token_match_some_eq_writeBits
            bw litLenCodes distCodes hlenInfo hdistInfo hlitBits
            hextraBits hdistBits hdistExtraBits
  · intro target htarget
    cases htok : source[target]'htarget with
    | literal b =>
        simpa [htok] using
          dynamicPayloadLz77TokenBits_generated_literal_lt_codeSpace_at
            source target b htarget htok
    | «match» len distance =>
        have hv := hvalid target htarget
        simp [Png.Lz77TokenFixedValid, htok] at hv
        rcases hv with
          ⟨hlenLo, hlenHi, distSym, distExtraBits, distExtraLen, hdistInfo⟩
        simpa [htok] using
          dynamicPayloadLz77TokenBits_generated_match_lt_codeSpace_at
            source target len distance htarget htok ⟨hlenLo, hlenHi⟩ hdistInfo

/-- Public greedy LZ77 tokens are fixed-valid: every match has a DEFLATE
length and encodable distance. This repackages the existing expansion proof
for generated dynamic payload writers. -/
lemma deflateTokensLz77_fixed_valid (raw : ByteArray) :
    ∀ target (htarget : target < (Png.deflateTokensLz77 raw).size),
      Png.Lz77TokenFixedValid ((Png.deflateTokensLz77 raw)[target]'htarget) := by
  let tokens := Png.deflateTokensLz77 raw
  have hexpand :
      Png.deflateTokensExpandLz77From? tokens 0 ByteArray.empty = some raw := by
    simpa [tokens, Png.deflateTokensExpandLz77?] using
      deflateTokensExpandLz77_deflateTokensLz77 raw
  intro target htarget
  exact
    Png.deflateTokensExpandLz77From?_fixed_valid tokens 0 ByteArray.empty raw
      hexpand target (Nat.zero_le target) htarget

/-- The public greedy LZ77 token stream writes exactly its generated dynamic
payload bit stream. This is the payload-writing specialization used by the
full dynamic encoder proof. -/
lemma writeDynamicPayloadLz77_deflateTokensLz77_eq_writeBits
    (raw : ByteArray) (bw : Png.BitWriter) :
    let source := Png.deflateTokensLz77 raw
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    Png.writeDynamicPayloadLz77 bw source litLenCodes distCodes =
      Png.BitWriter.writeBits bw
        (dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList)
        (dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList) := by
  intro source litLenCodes distCodes
  exact writeDynamicPayloadLz77_source_generated_eq_writeBits
    source
    (by
      intro target htarget
      simpa [source] using deflateTokensLz77_fixed_valid raw target (by
        simpa [source] using htarget))
    bw

/-- The generated LZ77 literal/length table keeps the EOB symbol in bounds.
This is the positive-entry witness used by dynamic table construction. -/
lemma generatedDynamicLitLenLengthsLz77_eob_inBounds
    (source : Array Png.Lz77Token) :
    256 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqsLz77 source)).size := by
  simp [generatedDynamicLitLenLengths_size, litLenSymbolFreqsLz77_size]

/-- The generated LZ77 literal/length table assigns EOB a positive length,
because the LZ77 frequency builder always increments the EOB bucket. -/
lemma generatedDynamicLitLenLengthsLz77_eob_pos
    (source : Array Png.Lz77Token) :
    0 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqsLz77 source))[256]'
          (generatedDynamicLitLenLengthsLz77_eob_inBounds source) := by
  let freqs := Png.litLenSymbolFreqsLz77 source
  let lengths := Png.generatedDynamicLitLenLengths freqs
  have hidx : 256 < freqs.size := by
    simpa [freqs, litLenSymbolFreqsLz77_size]
  have hpos : 0 < freqs[256]! := by
    simpa [freqs] using litLenSymbolFreqsLz77_eob_pos source
  have hiff :=
    generatedDynamicLitLenLengths_get!_pos_iff freqs 256 hidx
  have hposBang : 0 < lengths[256]! := by
    simpa [lengths] using hiff.mpr hpos
  have hidxLengths : 256 < lengths.size := by
    simpa [lengths, generatedDynamicLitLenLengths_size] using hidx
  rwa [getElem!_pos lengths 256 hidxLengths] at hposBang

/-- The generated LZ77 literal/length table assigns EOB the concrete nine-bit
code length. This fixes the max-code-length lower bound for `mkHuffman`. -/
lemma generatedDynamicLitLenLengthsLz77_eob_eq_nine
    (source : Array Png.Lz77Token) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqsLz77 source))[256]'
        (generatedDynamicLitLenLengthsLz77_eob_inBounds source) = 9 := by
  let freqs := Png.litLenSymbolFreqsLz77 source
  let lengths := Png.generatedDynamicLitLenLengths freqs
  have hidx : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengthsLz77_eob_inBounds source
  have hpos : 0 < lengths[256]'hidx := by
    simpa [lengths] using generatedDynamicLitLenLengthsLz77_eob_pos source
  have hiff :=
    generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine freqs 256 hidx
  simpa [lengths] using hiff.mp hpos

/-- Generated LZ77 literal/length tables scan to exactly the uniform nine-bit
code length. This is the LZ77 source-specific max scan fact for `mkHuffman`. -/
lemma maxCodeLenAux_generatedDynamicLitLenLengthsLz77_eq_codeLen
    (source : Array Png.Lz77Token) :
    Png.maxCodeLenAux
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqsLz77 source)) 0 0 =
      Png.generatedDynamicLitLenCodeLen := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  have hidx : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengthsLz77_eob_inBounds source
  have hentry : lengths[256] = Png.generatedDynamicLitLenCodeLen := by
    have heq := generatedDynamicLitLenLengthsLz77_eob_eq_nine source
    simpa [lengths, Png.generatedDynamicLitLenCodeLen] using heq
  have hle :
      Png.maxCodeLenAux lengths 0 0 ≤ Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_le_codeLen
        (Png.litLenSymbolFreqsLz77 source) 0 0
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have hge :
      Png.generatedDynamicLitLenCodeLen ≤ Png.maxCodeLenAux lengths 0 0 := by
    simpa [hentry] using getElem_le_maxCodeLenAux lengths 0 0 256 (by decide) hidx
  exact le_antisymm hle hge

/-- Generated LZ77 literal/length tables have strictly fewer entries than the
nine-bit code space. This is the non-oversubscription size side. -/
lemma generatedDynamicLitLenLengthsLz77_size_lt_codeSpace
    (source : Array Png.Lz77Token) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqsLz77 source)).size <
        2 ^ Png.generatedDynamicLitLenCodeLen := by
  simp [generatedDynamicLitLenLengths_size, litLenSymbolFreqsLz77_size,
    Png.generatedDynamicLitLenCodeLen]

/-- Generated LZ77 literal/length counts make the canonical scanned max code
start at zero. This adapts the generic generated next-code fact to LZ77. -/
lemma nextCodesAux_generatedDynamicLitLenLengthsLz77_get!_scannedMax_eq_zero
    (source : Array Png.Lz77Token) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let maxLen := Png.maxCodeLenAux lengths 0 0
    let count :=
      Png.countCodeLengthsAux lengths 0 (Array.replicate (maxLen + 1) 0)
    let nextCode0 := Array.replicate (maxLen + 1) 0
    let nextCode := (Png.nextCodesAux count maxLen 1 0 nextCode0).2
    nextCode[maxLen]! = 0 := by
  intro lengths maxLen count nextCode0 nextCode
  have hmax :
      maxLen = Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths, maxLen] using
      maxCodeLenAux_generatedDynamicLitLenLengthsLz77_eq_codeLen source
  simpa [lengths, maxLen, count, nextCode0, nextCode, hmax] using
    nextCodesAux_generatedDynamicLitLenLengths_get!_codeLen_eq_zero
      (Png.litLenSymbolFreqsLz77 source)

/-- LZ77 generated literal/length lengths are accepted by `mkHuffman`.
This names the successful table construction for later payload replay. -/
lemma mkHuffman_generatedDynamicLitLenLengthsLz77_isSome
    (source : Array Png.Lz77Token) :
    (Png.mkHuffman
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqsLz77 source))).isSome = true := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  let maxLen := Png.maxCodeLenAux lengths 0 0
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate (maxLen + 1) 0)
  let nextCode0 : Array Nat := Array.replicate (maxLen + 1) 0
  let nextCode := (Png.nextCodesAux count maxLen 1 0 nextCode0).2
  let codeLen := Png.generatedDynamicLitLenCodeLen
  have hmax : maxLen = codeLen := by
    simpa [lengths, maxLen, codeLen] using
      maxCodeLenAux_generatedDynamicLitLenLengthsLz77_eq_codeLen source
  have hmaxNe : ¬ maxLen = 0 := by
    rw [hmax]
    exact Nat.ne_of_gt (by simpa [codeLen] using generatedDynamicLitLenCodeLen_pos)
  have hnextSize : nextCode.size = nextCode0.size := by
    simpa [nextCode] using nextCodesAux_size count maxLen 1 0 nextCode0
  have hnextIdx : codeLen < nextCode.size := by
    rw [hnextSize]
    simp [nextCode0, hmax, codeLen]
  have htableIdx : codeLen < (Png.huffmanEmptyTable maxLen).size := by
    simp [huffmanEmptyTable_size, hmax, codeLen]
  have hrow :
      (Png.huffmanEmptyTable maxLen)[codeLen]!.size = 1 <<< codeLen := by
    exact huffmanEmptyTable_get!_size maxLen codeLen (by simp [hmax])
      (by simpa [codeLen] using generatedDynamicLitLenCodeLen_pos)
  have hnextZero : nextCode[codeLen]! = 0 := by
    have hscanned :=
      nextCodesAux_generatedDynamicLitLenLengthsLz77_get!_scannedMax_eq_zero source
    simpa [lengths, maxLen, count, nextCode0, nextCode, codeLen, hmax] using hscanned
  have hsizeLt : lengths.size < 1 <<< codeLen := by
    have hlt := generatedDynamicLitLenLengthsLz77_size_lt_codeSpace source
    simpa [lengths, codeLen, Nat.shiftLeft_eq] using hlt
  have hbudget : nextCode[codeLen]! + (lengths.size - 0) ≤ 1 <<< codeLen := by
    rw [hnextZero]
    omega
  have hshape :
      ∀ j (hj : j < lengths.size), 0 ≤ j →
        0 < lengths[j] → lengths[j] = codeLen := by
    intro j hj _hle hpos
    have hnine :
        lengths[j] = 9 := by
      simpa [lengths] using
        (generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
          (Png.litLenSymbolFreqsLz77 source) j (by simpa [lengths] using hj)).mp hpos
    simpa [codeLen, generatedDynamicLitLenCodeLen_eq_nine] using hnine
  have hfill :
      (Png.fillHuffmanTableAux lengths 0 nextCode
        (Png.huffmanEmptyTable maxLen)).isSome = true :=
    fillHuffmanTableAux_uniform_isSome lengths 0 codeLen nextCode
      (Png.huffmanEmptyTable maxLen) hshape hnextIdx htableIdx hrow hbudget
  obtain ⟨table, hfillEq⟩ :
      ∃ table,
        Png.fillHuffmanTableAux lengths 0 nextCode
          (Png.huffmanEmptyTable maxLen) = some table := by
    cases h :
        Png.fillHuffmanTableAux lengths 0 nextCode
          (Png.huffmanEmptyTable maxLen) with
    | none =>
        simp [h] at hfill
    | some table =>
        exact ⟨table, rfl⟩
  change (Png.mkHuffman lengths).isSome = true
  simp [Png.mkHuffman, maxLen, count, nextCode0, nextCode, hmaxNe, hfillEq]

/-- `mkHuffman` produces the named LZ77 generated literal/length Huffman
table. This gives later lemmas a stable table name. -/
def generatedDynamicLitLenTableLz77
    (source : Array Png.Lz77Token) : Png.Huffman :=
  match Png.mkHuffman
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqsLz77 source)) with
  | some table => table
  | none => { maxLen := 0, table := #[] }

/-- The LZ77 generated literal/length table name unfolds to the successful
runtime `mkHuffman` result. -/
lemma mkHuffman_generatedDynamicLitLenLengthsLz77_eq
    (source : Array Png.Lz77Token) :
    Png.mkHuffman
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqsLz77 source)) =
      some (generatedDynamicLitLenTableLz77 source) := by
  have hsome :=
    mkHuffman_generatedDynamicLitLenLengthsLz77_isSome source
  cases h :
      Png.mkHuffman
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqsLz77 source)) with
  | none =>
      simp [h] at hsome
  | some table =>
      simp [generatedDynamicLitLenTableLz77, h]

/-- Proof-only projection from full LZ77 tokens to the legacy distance-1 token
shape. It preserves exactly the literal/length symbols and discards distance. -/
def lz77LitLenMirrorToken : Png.Lz77Token → Png.DeflateToken
  | .literal b => .literal b
  | .match len _distance => .matchDist1 len

/-- Proof-only token stream used to reuse legacy literal/length dynamic-table
lemmas. It mirrors literals and match lengths while ignoring match distances. -/
def lz77LitLenMirrorTokens
    (tokens : Array Png.Lz77Token) : Array Png.DeflateToken :=
  Array.ofFn fun idx : Fin tokens.size =>
    lz77LitLenMirrorToken tokens[idx]

/-- The proof-only literal/length mirror has the same number of tokens as the
full LZ77 source stream. -/
lemma lz77LitLenMirrorTokens_size
    (tokens : Array Png.Lz77Token) :
    (lz77LitLenMirrorTokens tokens).size = tokens.size := by
  simp [lz77LitLenMirrorTokens]

/-- Indexing the literal/length mirror is the same as projecting the indexed
LZ77 token. This is the bridge for reusing legacy token-indexed lemmas. -/
lemma lz77LitLenMirrorTokens_get
    (tokens : Array Png.Lz77Token) (idx : Nat) (hidx : idx < tokens.size) :
    (lz77LitLenMirrorTokens tokens)[idx]'
        (by simpa [lz77LitLenMirrorTokens_size] using hidx) =
      lz77LitLenMirrorToken (tokens[idx]'hidx) := by
  simp [lz77LitLenMirrorTokens]

/-- Literal/length frequency scanning is unchanged by the proof-only mirror.
This lets LZ77 generated literal/length tables reuse the legacy table proofs. -/
lemma litLenSymbolFreqs_lz77LitLenMirrorTokensAux
    (tokens : Array Png.Lz77Token) (i : Nat) (freqs : Array Nat) :
    Png.litLenSymbolFreqsAux (lz77LitLenMirrorTokens tokens) i freqs =
      Png.litLenSymbolFreqsLz77Aux tokens i freqs := by
  rw [Png.litLenSymbolFreqsAux.eq_1, Png.litLenSymbolFreqsLz77Aux.eq_1]
  by_cases h : i < tokens.size
  · have hmirror : i < (lz77LitLenMirrorTokens tokens).size := by
      simpa [lz77LitLenMirrorTokens_size] using h
    cases htok : tokens[i]'h with
    | literal b =>
        have hget :
            (lz77LitLenMirrorTokens tokens)[i]'hmirror =
              Png.DeflateToken.literal b := by
          simpa [lz77LitLenMirrorToken, htok] using
            lz77LitLenMirrorTokens_get tokens i h
        have hrec :=
          litLenSymbolFreqs_lz77LitLenMirrorTokensAux tokens (i + 1)
            (Png.incrementNatAt freqs b.toNat)
        simpa [h, hmirror, hget, htok] using hrec
    | «match» len distance =>
        have hget :
            (lz77LitLenMirrorTokens tokens)[i]'hmirror =
              Png.DeflateToken.matchDist1 len := by
          simpa [lz77LitLenMirrorToken, htok] using
            lz77LitLenMirrorTokens_get tokens i h
        have hrec :=
          litLenSymbolFreqs_lz77LitLenMirrorTokensAux tokens (i + 1)
            (Png.incrementNatAt freqs (Png.deflateLengthInfo len).1)
        simpa [h, hmirror, hget, htok, Png.deflateLengthInfo] using hrec
  · have hmirror : ¬ i < (lz77LitLenMirrorTokens tokens).size := by
      simpa [lz77LitLenMirrorTokens_size] using h
    simp [h, hmirror]
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Completed literal/length frequency tables are unchanged by the proof-only
mirror, including the final EOB increment. -/
lemma litLenSymbolFreqs_lz77LitLenMirrorTokens
    (tokens : Array Png.Lz77Token) :
    Png.litLenSymbolFreqs (lz77LitLenMirrorTokens tokens) =
      Png.litLenSymbolFreqsLz77 tokens := by
  simp [Png.litLenSymbolFreqs, Png.litLenSymbolFreqsLz77,
    litLenSymbolFreqs_lz77LitLenMirrorTokensAux]

/-- The LZ77 generated literal/length Huffman table is the legacy generated
table for the proof-only literal/length mirror. -/
lemma generatedDynamicLitLenTableLz77_eq_lz77LitLenMirrorTokens
    (source : Array Png.Lz77Token) :
    generatedDynamicLitLenTableLz77 source =
      generatedDynamicLitLenTable (lz77LitLenMirrorTokens source) := by
  have hold :
      Png.mkHuffman
          (Png.generatedDynamicLitLenLengths
            (Png.litLenSymbolFreqsLz77 source)) =
        some (generatedDynamicLitLenTable (lz77LitLenMirrorTokens source)) := by
    simpa [litLenSymbolFreqs_lz77LitLenMirrorTokens source] using
      mkHuffman_generatedDynamicLitLenLengths_eq
        (lz77LitLenMirrorTokens source)
  have hlz :=
    mkHuffman_generatedDynamicLitLenLengthsLz77_eq source
  rw [hlz] at hold
  simpa using hold

/-- A generated LZ77 literal token's literal/length code decodes through the
LZ77 generated table by reusing the legacy mirror table proof. -/
lemma generatedDynamicLitLenTableLz77_decode_literal_at_readerAt_writeBits
    (source : Array Png.Lz77Token) (target : Nat) (b : UInt8)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.literal b)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let bitsTot := codes[b.toNat]!.1 ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    (generatedDynamicLitLenTableLz77 source).decode br0 =
      some (b.toNat, br9) := by
  intro lengths codes bitsTot lenTot bw' br0 br9
  let mirror := lz77LitLenMirrorTokens source
  have htargetMirror : target < mirror.size := by
    simpa [mirror, lz77LitLenMirrorTokens_size] using htarget
  have htMirror : mirror[target]'htargetMirror = Png.DeflateToken.literal b := by
    simpa [mirror, lz77LitLenMirrorToken, ht] using
      lz77LitLenMirrorTokens_get source target htarget
  have hdecode :=
    generatedDynamicLitLenTable_decode_literal_at_readerAt_writeBits
      (tokens := mirror) (target := target) (b := b) (bw := bw)
      (restBits := restBits) (restLen := restLen)
      htargetMirror htMirror hbit hcur
  simpa [mirror, litLenSymbolFreqs_lz77LitLenMirrorTokens,
    generatedDynamicLitLenTableLz77_eq_lz77LitLenMirrorTokens,
    lengths, codes, bitsTot, lenTot, bw', br0, br9] using hdecode

/-- A generated LZ77 match token's length symbol decodes through the LZ77
generated table. Distance decoding is handled by separate distance-table lemmas. -/
lemma generatedDynamicLitLenTableLz77_decode_match_at_readerAt_writeBits
    (source : Array Png.Lz77Token) (target len distance : Nat)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let sym := (Png.deflateLengthInfo len).1
    let bitsTot := codes[sym]!.1 ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    (generatedDynamicLitLenTableLz77 source).decode br0 = some (sym, br9) := by
  intro lengths codes sym bitsTot lenTot bw' br0 br9
  let mirror := lz77LitLenMirrorTokens source
  have htargetMirror : target < mirror.size := by
    simpa [mirror, lz77LitLenMirrorTokens_size] using htarget
  have htMirror : mirror[target]'htargetMirror = Png.DeflateToken.matchDist1 len := by
    simpa [mirror, lz77LitLenMirrorToken, ht] using
      lz77LitLenMirrorTokens_get source target htarget
  have hdecode :=
    generatedDynamicLitLenTable_decode_match_at_readerAt_writeBits
      (tokens := mirror) (target := target) (len := len) (bw := bw)
      (restBits := restBits) (restLen := restLen)
      htargetMirror htMirror hlen hbit hcur
  simpa [mirror, Png.deflateLengthInfo,
    litLenSymbolFreqs_lz77LitLenMirrorTokens,
    generatedDynamicLitLenTableLz77_eq_lz77LitLenMirrorTokens,
    lengths, codes, sym, bitsTot, lenTot, bw', br0, br9] using hdecode

/-- The generated LZ77 EOB literal/length code decodes through the LZ77 table.
This is the terminal literal/length decode step for LZ77 dynamic payload traces. -/
lemma generatedDynamicLitLenTableLz77_decode_eob_readerAt_writeBits
    (source : Array Png.Lz77Token)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let bitsTot := codes[256]!.1 ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    (generatedDynamicLitLenTableLz77 source).decode br0 = some (256, br9) := by
  intro lengths codes bitsTot lenTot bw' br0 br9
  let mirror := lz77LitLenMirrorTokens source
  have hdecode :=
    generatedDynamicLitLenTable_decode_eob_readerAt_writeBits
      (tokens := mirror) (bw := bw) (restBits := restBits)
      (restLen := restLen) hbit hcur
  simpa [mirror, litLenSymbolFreqs_lz77LitLenMirrorTokens,
    generatedDynamicLitLenTableLz77_eq_lz77LitLenMirrorTokens,
    lengths, codes, bitsTot, lenTot, bw', br0, br9] using hdecode

/-- LZ77 dynamic distance code-length arrays obey the DEFLATE 15-bit bound.
The v1 encoder advertises a uniform five-bit table for all distance symbols. -/
lemma generatedDynamicDistLengthsLz77_entries_le_15
    (freqs : Array Nat) :
    ArrayEntriesLe (Png.generatedDynamicDistLengthsLz77 freqs) 15 := by
  intro idx hidx
  have hlen : (Png.generatedDynamicDistLengthsLz77 freqs)[idx]! = 5 := by
    exact generatedDynamicDistLengthsLz77_get!_eq_five freqs idx hidx
  rw [getElem!_pos (Png.generatedDynamicDistLengthsLz77 freqs) idx hidx] at hlen
  omega

/-- Named dynamic distance Huffman table for v1 LZ77 blocks. It is built from
the uniform 30-symbol, five-bit distance length array advertised by the encoder. -/
def generatedDynamicDistTableLz77 : Png.Huffman :=
  match Png.mkHuffman (Array.replicate 30 5) with
  | some table => table
  | none => Png.emptyHuffman

/-- The v1 LZ77 generated distance lengths build the named five-bit table.
This packages the runtime `mkHuffman` result for later payload replay. -/
lemma mkHuffman_generatedDynamicDistLengthsLz77_eq
    (freqs : Array Nat) :
    Png.mkHuffman (Png.generatedDynamicDistLengthsLz77 freqs) =
      some generatedDynamicDistTableLz77 := by
  unfold Png.generatedDynamicDistLengthsLz77 generatedDynamicDistTableLz77
  native_decide

/-- Runtime dynamic distance-table construction accepts the v1 LZ77 distance
lengths and returns the named generated table. -/
lemma buildDynamicDistTable_generatedDynamicDistLengthsLz77_eq
    (freqs : Array Nat) :
    Png.buildDynamicDistTable (Png.generatedDynamicDistLengthsLz77 freqs) =
      some generatedDynamicDistTableLz77 := by
  simp [Png.buildDynamicDistTable,
    mkHuffman_generatedDynamicDistLengthsLz77_eq freqs]

/-- The v1 LZ77 generated distance table has five-bit maximum code length. -/
lemma generatedDynamicDistTableLz77_maxLen :
    generatedDynamicDistTableLz77.maxLen = 5 := by
  native_decide

/-- The v1 LZ77 generated distance table has rows zero through five. -/
lemma generatedDynamicDistTableLz77_table_size :
    generatedDynamicDistTableLz77.table.size = 6 := by
  native_decide

/-- The v1 LZ77 generated distance table's final row has the full five-bit
code-space width. -/
lemma generatedDynamicDistTableLz77_row5_size :
    generatedDynamicDistTableLz77.table[5]!.size = 1 <<< 5 := by
  native_decide

/-- Rows shorter than five bits in the LZ77 generated distance table keep their
initialized widths. These rows cannot resolve a distance symbol. -/
lemma generatedDynamicDistTableLz77_short_row_size
    (rowIdx : Nat) (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 5) :
    generatedDynamicDistTableLz77.table[rowIdx]!.size = 1 <<< rowIdx := by
  have hcases :
      rowIdx = 1 ∨ rowIdx = 2 ∨ rowIdx = 3 ∨ rowIdx = 4 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl <;> native_decide

/-- Rows shorter than five bits in the LZ77 generated distance table contain no
symbols. Huffman decoding must continue until row five. -/
lemma generatedDynamicDistTableLz77_short_row_get_none
    (rowIdx code : Nat) (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 5)
    (hcode : code < generatedDynamicDistTableLz77.table[rowIdx]!.size) :
    generatedDynamicDistTableLz77.table[rowIdx]![code]! = none := by
  have hcases :
      rowIdx = 1 ∨ rowIdx = 2 ∨ rowIdx = 3 ∨ rowIdx = 4 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hrow :
        generatedDynamicDistTableLz77.table[1]! =
          Array.replicate (1 <<< 1) (none : Option Nat) := by
      native_decide
    have hcodeRep :
        code < (Array.replicate (1 <<< 1) (none : Option Nat)).size := by
      simpa [hrow] using hcode
    rw [hrow]
    rw [getElem!_pos
      (Array.replicate (1 <<< 1) (none : Option Nat)) code hcodeRep]
    simp
  · have hrow :
        generatedDynamicDistTableLz77.table[2]! =
          Array.replicate (1 <<< 2) (none : Option Nat) := by
      native_decide
    have hcodeRep :
        code < (Array.replicate (1 <<< 2) (none : Option Nat)).size := by
      simpa [hrow] using hcode
    rw [hrow]
    rw [getElem!_pos
      (Array.replicate (1 <<< 2) (none : Option Nat)) code hcodeRep]
    simp
  · have hrow :
        generatedDynamicDistTableLz77.table[3]! =
          Array.replicate (1 <<< 3) (none : Option Nat) := by
      native_decide
    have hcodeRep :
        code < (Array.replicate (1 <<< 3) (none : Option Nat)).size := by
      simpa [hrow] using hcode
    rw [hrow]
    rw [getElem!_pos
      (Array.replicate (1 <<< 3) (none : Option Nat)) code hcodeRep]
    simp
  · have hrow :
        generatedDynamicDistTableLz77.table[4]! =
          Array.replicate (1 <<< 4) (none : Option Nat) := by
      native_decide
    have hcodeRep :
        code < (Array.replicate (1 <<< 4) (none : Option Nat)).size := by
      simpa [hrow] using hcode
    rw [hrow]
    rw [getElem!_pos
      (Array.replicate (1 <<< 4) (none : Option Nat)) code hcodeRep]
    simp

/-- The LZ77 generated distance table maps every positive generated canonical
five-bit distance code back to its distance symbol. -/
lemma generatedDynamicDistTableLz77_lookup_generated_code
    (freqs : Array Nat) (sym : Nat)
    (hsym : sym < (Png.generatedDynamicDistLengthsLz77 freqs).size) :
    let lengths := Png.generatedDynamicDistLengthsLz77 freqs
    let codes := Png.canonicalRevCodesFromLengths lengths
    generatedDynamicDistTableLz77.table[5]![codes[sym]!.1]! =
      some sym := by
  intro lengths codes
  have hmk :
      Png.mkHuffman lengths = some generatedDynamicDistTableLz77 := by
    simpa [lengths] using mkHuffman_generatedDynamicDistLengthsLz77_eq freqs
  have hmax :
      Png.maxCodeLenAux lengths 0 0 = 5 := by
    simpa [lengths, Png.generatedDynamicDistLengthsLz77] using
      (show Png.maxCodeLenAux (Array.replicate 30 5) 0 0 = 5 by
        native_decide)
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate (5 + 1) 0)
  let nextCode0 : Array Nat := Array.replicate (5 + 1) 0
  let nextCode := (Png.nextCodesAux count 5 1 0 nextCode0).2
  let init := Png.huffmanEmptyTable 5
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 5, table := table } : Png.Huffman)) =
        some generatedDynamicDistTableLz77 := by
    simpa [Png.mkHuffman, lengths, hmax, count, nextCode0, nextCode, init]
      using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hshape :
          ∀ j (hj : j < lengths.size), 0 ≤ j →
            0 < lengths[j] → lengths[j] = 5 := by
        intro j hj _hle _hpos
        have hlen : lengths[j]! = 5 := by
          simpa [lengths] using
            generatedDynamicDistLengthsLz77_get!_eq_five freqs j
              (by simpa [lengths] using hj)
        rw [getElem!_pos lengths j hj] at hlen
        exact hlen
      have hnextSize : nextCode.size = nextCode0.size := by
        simpa [nextCode] using nextCodesAux_size count 5 1 0 nextCode0
      have hnextIdx : 5 < nextCode.size := by
        rw [hnextSize]
        simp [nextCode0]
      have htableIdx : 5 < init.size := by
        simp [init, huffmanEmptyTable_size]
      have hrow : init[5]!.size = 1 <<< 5 := by
        exact huffmanEmptyTable_get!_size 5 5 le_rfl (by decide)
      have hnextZero : nextCode[5]! = 0 := by
        simpa [lengths, count, nextCode0, nextCode,
          Png.generatedDynamicDistLengthsLz77] using
          (show
            (Png.nextCodesAux
              (Png.countCodeLengthsAux (Array.replicate 30 5) 0
                (Array.replicate (5 + 1) 0))
              5 1 0 (Array.replicate (5 + 1) 0)).2[5]! = 0 by
              native_decide)
      have hbudget : nextCode[5]! + (lengths.size - 0) ≤ 1 <<< 5 := by
        rw [hnextZero]
        simp [lengths, Png.generatedDynamicDistLengthsLz77]
      have hposTarget : 0 < lengths[sym] := by
        have hlen : lengths[sym]! = 5 := by
          simpa [lengths] using
            generatedDynamicDistLengthsLz77_get!_eq_five freqs sym
              (by simpa [lengths] using hsym)
        rw [getElem!_pos lengths sym (by simpa [lengths] using hsym)] at hlen
        omega
      have hlookup :=
        fillHuffmanTableAux_uniform_lookup_of_canonical_at
          lengths 0 5 nextCode init table
          (Array.replicate lengths.size (0, 0)) sym hshape
          hnextIdx htableIdx hrow hbudget
          (by simpa [lengths] using hsym) (Nat.zero_le sym) (by simp)
          hposTarget hfill
      simp [hfill] at hmk'
      rw [← hmk']
      simpa [codes, Png.canonicalRevCodesFromLengths, lengths, count,
        nextCode0, nextCode, hmax] using hlookup

/-- Appending later payload bits after a generated five-bit distance code
preserves row-five lookup in the LZ77 generated distance table. -/
lemma generatedDynamicDistTableLz77_prefix5_row_some
    (freqs : Array Nat) (sym restBits : Nat)
    (hsym : sym < (Png.generatedDynamicDistLengthsLz77 freqs).size) :
    let lengths := Png.generatedDynamicDistLengthsLz77 freqs
    let codes := Png.canonicalRevCodesFromLengths lengths
    let bitsTot := codes[sym]!.1 ||| (restBits <<< 5)
    generatedDynamicDistTableLz77.table[5]![bitsTot % 2 ^ 5]! =
      some sym := by
  intro lengths codes bitsTot
  have hlookup :=
    generatedDynamicDistTableLz77_lookup_generated_code freqs sym hsym
  have hbits :
      codes[sym]!.1 < 2 ^ 5 := by
    simpa [lengths, codes] using
      generatedDynamicDistCodesLz77_bits_lt_codeSpace freqs sym hsym
  have hmod :
      (codes[sym]!.1 ||| (restBits <<< 5)) % 2 ^ 5 =
        codes[sym]!.1 := by
    have h :=
      Png.mod_two_pow_or_shift
        (a := codes[sym]!.1) (b := restBits) (k := 5) (len := 5) le_rfl
    have hmodCode : codes[sym]!.1 % 2 ^ 5 = codes[sym]!.1 :=
      Nat.mod_eq_of_lt hbits
    simpa [hmodCode] using h
  simpa [lengths, codes, bitsTot, hmod] using hlookup

/-- Any LZ77 generated distance prefix shorter than five bits is unresolved.
This is the packed-stream row fact used by the distance decoder replay. -/
lemma generatedDynamicDistTableLz77_prefix_row_none
    (bitsTot rowIdx : Nat) (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 5) :
    generatedDynamicDistTableLz77.table[rowIdx]![bitsTot % 2 ^ rowIdx]! =
      none := by
  have hsize :=
    generatedDynamicDistTableLz77_short_row_size rowIdx hrowPos hrowLt
  have hcode :
      bitsTot % 2 ^ rowIdx <
        generatedDynamicDistTableLz77.table[rowIdx]!.size := by
    have hpow : 0 < 2 ^ rowIdx := Nat.pow_pos (by decide : 0 < (2 : Nat))
    have hmod : bitsTot % 2 ^ rowIdx < 2 ^ rowIdx := Nat.mod_lt bitsTot hpow
    simpa [hsize, Nat.shiftLeft_eq] using hmod
  exact generatedDynamicDistTableLz77_short_row_get_none rowIdx
    (bitsTot % 2 ^ rowIdx) hrowPos hrowLt hcode

/-- Short LZ77 distance prefixes fit in their internal decode rows. This gives
`decodeFuel` the array-bound proof for rows one through four. -/
lemma generatedDynamicDistTableLz77_prefix_code_lt_row_size
    (bitsTot rowIdx : Nat) (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 5)
    (htable : rowIdx < generatedDynamicDistTableLz77.table.size) :
    bitsTot % 2 ^ rowIdx <
      (Array.getInternal generatedDynamicDistTableLz77.table rowIdx htable).size := by
  have hrowGet :
      generatedDynamicDistTableLz77.table[rowIdx]! =
        Array.getInternal generatedDynamicDistTableLz77.table rowIdx htable := by
    rw [getElem!_pos generatedDynamicDistTableLz77.table rowIdx htable]
    rfl
  have hsize :=
    generatedDynamicDistTableLz77_short_row_size rowIdx hrowPos hrowLt
  have hlt : bitsTot % 2 ^ rowIdx < 2 ^ rowIdx :=
    Nat.mod_lt bitsTot (Nat.pow_pos (by decide : 0 < (2 : Nat)))
  rw [← hrowGet]
  simpa [hsize, Nat.shiftLeft_eq] using hlt

/-- A generated LZ77 five-bit distance prefix fits in row five. This supplies
the final-row bound before the successful `decodeFuel` step. -/
lemma generatedDynamicDistTableLz77_prefix5_code_lt_row_size
    (bitsTot : Nat)
    (htable : 5 < generatedDynamicDistTableLz77.table.size) :
    bitsTot % 2 ^ 5 <
      (Array.getInternal generatedDynamicDistTableLz77.table 5 htable).size := by
  have hrowGet :
      generatedDynamicDistTableLz77.table[5]! =
        Array.getInternal generatedDynamicDistTableLz77.table 5 htable := by
    rw [getElem!_pos generatedDynamicDistTableLz77.table 5 htable]
    rfl
  have hlt : bitsTot % 2 ^ 5 < 1 <<< 5 := by
    simpa [Nat.shiftLeft_eq] using
      Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 5)
  rw [← hrowGet]
  simpa [generatedDynamicDistTableLz77_row5_size] using hlt

/-- Internal-row form of unresolved LZ77 distance prefixes for rows shorter
than five bits. -/
lemma generatedDynamicDistTableLz77_prefix_row_none_internal
    (bitsTot rowIdx : Nat) (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 5)
    (htable : rowIdx < generatedDynamicDistTableLz77.table.size)
    (hcode :
      bitsTot % 2 ^ rowIdx <
        (Array.getInternal generatedDynamicDistTableLz77.table rowIdx htable).size) :
    Array.getInternal
      (Array.getInternal generatedDynamicDistTableLz77.table rowIdx htable)
      (bitsTot % 2 ^ rowIdx) hcode = none := by
  have hrowGet :
      generatedDynamicDistTableLz77.table[rowIdx]! =
        Array.getInternal generatedDynamicDistTableLz77.table rowIdx htable := by
    rw [getElem!_pos generatedDynamicDistTableLz77.table rowIdx htable]
    rfl
  have hentry :
      generatedDynamicDistTableLz77.table[rowIdx]![bitsTot % 2 ^ rowIdx]! =
        Array.getInternal
          (Array.getInternal generatedDynamicDistTableLz77.table rowIdx htable)
          (bitsTot % 2 ^ rowIdx) hcode := by
    rw [hrowGet]
    rw [getElem!_pos
      (Array.getInternal generatedDynamicDistTableLz77.table rowIdx htable)
      (bitsTot % 2 ^ rowIdx) hcode]
    rfl
  have hp :=
    generatedDynamicDistTableLz77_prefix_row_none bitsTot rowIdx hrowPos hrowLt
  rw [hentry] at hp
  exact hp

/-- Internal-row form of a successful LZ77 distance row-five lookup. -/
lemma generatedDynamicDistTableLz77_prefix5_row_some_internal
    (bitsTot sym : Nat)
    (hrow5 :
      generatedDynamicDistTableLz77.table[5]![bitsTot % 2 ^ 5]! = some sym)
    (htable : 5 < generatedDynamicDistTableLz77.table.size)
    (hcode :
      bitsTot % 2 ^ 5 <
        (Array.getInternal generatedDynamicDistTableLz77.table 5 htable).size) :
    Array.getInternal
      (Array.getInternal generatedDynamicDistTableLz77.table 5 htable)
      (bitsTot % 2 ^ 5) hcode = some sym := by
  have hrowGet :
      generatedDynamicDistTableLz77.table[5]! =
        Array.getInternal generatedDynamicDistTableLz77.table 5 htable := by
    rw [getElem!_pos generatedDynamicDistTableLz77.table 5 htable]
    rfl
  have hentry :
      generatedDynamicDistTableLz77.table[5]![bitsTot % 2 ^ 5]! =
        Array.getInternal
          (Array.getInternal generatedDynamicDistTableLz77.table 5 htable)
          (bitsTot % 2 ^ 5) hcode := by
    rw [hrowGet]
    rw [getElem!_pos
      (Array.getInternal generatedDynamicDistTableLz77.table 5 htable)
      (bitsTot % 2 ^ 5) hcode]
    rfl
  rw [hentry] at hrow5
  exact hrow5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2500000 in
/-- Decodes a generated five-bit LZ77 distance code from a writer-built stream.
This is the dynamic-distance counterpart of the literal/length decode bridge. -/
lemma generatedDynamicDistTableLz77_decode_readerAt_writeBits_core
    (bw : Png.BitWriter) (bitsTot restLen sym : Nat)
    (hrow5 :
      generatedDynamicDistTableLz77.table[5]![bitsTot % 2 ^ 5]! = some sym)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lenTot := 5 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br5 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    generatedDynamicDistTableLz77.decode br0 = some (sym, br5) := by
  let lenTot := 5 + restLen
  let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
  let bw1 := Png.BitWriter.writeBits bw bitsTot 1
  let bw2 := Png.BitWriter.writeBits bw bitsTot 2
  let bw3 := Png.BitWriter.writeBits bw bitsTot 3
  let bw4 := Png.BitWriter.writeBits bw bitsTot 4
  let bw5 := Png.BitWriter.writeBits bw bitsTot 5
  let br0 := Png.BitWriter.readerAt bw bw'.flush
    (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br1 := Png.BitWriter.readerAt bw1 bw'.flush
    (by
      have hk : 1 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  let br2 := Png.BitWriter.readerAt bw2 bw'.flush
    (by
      have hk : 2 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  let br3 := Png.BitWriter.readerAt bw3 bw'.flush
    (by
      have hk : 3 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 3 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 3 hbit)
  let br4 := Png.BitWriter.readerAt bw4 bw'.flush
    (by
      have hk : 4 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 4 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 4 hbit)
  let br5 := Png.BitWriter.readerAt bw5 bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hbit1 : bw1.bitPos < 8 := by
    simpa [bw1] using Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit
  have hbit2 : bw2.bitPos < 8 := by
    simpa [bw2] using Png.bitPos_lt_8_writeBits bw bitsTot 2 hbit
  have hbit3 : bw3.bitPos < 8 := by
    simpa [bw3] using Png.bitPos_lt_8_writeBits bw bitsTot 3 hbit
  have hbit4 : bw4.bitPos < 8 := by
    simpa [bw4] using Png.bitPos_lt_8_writeBits bw bitsTot 4 hbit
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using Png.curClearAbove_writeBits bw bitsTot 1 hbit hcur
  have hcur2 : bw2.curClearAbove := by
    simpa [bw2] using Png.curClearAbove_writeBits bw bitsTot 2 hbit hcur
  have hcur3 : bw3.curClearAbove := by
    simpa [bw3] using Png.curClearAbove_writeBits bw bitsTot 3 hbit hcur
  have hcur4 : bw4.curClearAbove := by
    simpa [bw4] using Png.curClearAbove_writeBits bw bitsTot 4 hbit hcur
  have hsplit1 : bw' = Png.BitWriter.writeBits bw1 (bitsTot >>> 1) (lenTot - 1) := by
    have hk : 1 + (lenTot - 1) = lenTot := by omega
    simpa [bw', bw1, hk] using
      (Png.writeBits_split bw bitsTot 1 (lenTot - 1))
  have hsplit2 : bw' = Png.BitWriter.writeBits bw2 (bitsTot >>> 2) (lenTot - 2) := by
    have hk : 2 + (lenTot - 2) = lenTot := by omega
    simpa [bw', bw2, hk] using
      (Png.writeBits_split bw bitsTot 2 (lenTot - 2))
  have hsplit3 : bw' = Png.BitWriter.writeBits bw3 (bitsTot >>> 3) (lenTot - 3) := by
    have hk : 3 + (lenTot - 3) = lenTot := by omega
    simpa [bw', bw3, hk] using
      (Png.writeBits_split bw bitsTot 3 (lenTot - 3))
  have hsplit4 : bw' = Png.BitWriter.writeBits bw4 (bitsTot >>> 4) (lenTot - 4) := by
    have hk : 4 + (lenTot - 4) = lenTot := by omega
    simpa [bw', bw4, hk] using
      (Png.writeBits_split bw bitsTot 4 (lenTot - 4))
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, bw', lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot)
        (k := 1) (by omega) hbit)
  have hbound1 : br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, bw', hsplit1, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw1) (bits := bitsTot >>> 1)
        (len := lenTot - 1) (k := 1) (by omega) hbit1)
  have hbound2 : br2.bitIndex + 1 ≤ br2.data.size * 8 := by
    simpa [br2, bw', hsplit2, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw2) (bits := bitsTot >>> 2)
        (len := lenTot - 2) (k := 1) (by omega) hbit2)
  have hbound3 : br3.bitIndex + 1 ≤ br3.data.size * 8 := by
    simpa [br3, bw', hsplit3, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw3) (bits := bitsTot >>> 3)
        (len := lenTot - 3) (k := 1) (by omega) hbit3)
  have hbound4 : br4.bitIndex + 1 ≤ br4.data.size * 8 := by
    simpa [br4, bw', hsplit4, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw4) (bits := bitsTot >>> 4)
        (len := lenTot - 4) (k := 1) (by omega) hbit4)
  have hread0 : br0.readBit = (bitsTot % 2, br1) := by
    simpa [br0, br1, bw', lenTot] using
      (Png.readBit_readerAt_writeBits (bw := bw) (bits := bitsTot)
        (len := lenTot) hbit hcur (by omega))
  have hbw2 : Png.BitWriter.writeBit bw1 ((bitsTot >>> 1) % 2) = bw2 := by
    simp [bw1, bw2, Png.BitWriter.writeBits]
  have hread1 : br1.readBit = ((bitsTot >>> 1) % 2, br2) := by
    simpa [br1, br2, bw', hsplit1, hbw2, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1)
        hbit1 hcur1 (by omega))
  have hshift2 : bitsTot >>> 1 >>> 1 = bitsTot >>> 2 := by
    simpa using (Nat.shiftRight_add bitsTot 1 1)
  have hbw3 : Png.BitWriter.writeBit bw2 ((bitsTot >>> 2) % 2) = bw3 := by
    simp [bw2, bw3, Png.BitWriter.writeBits, hshift2]
  have hread2 : br2.readBit = ((bitsTot >>> 2) % 2, br3) := by
    simpa [br2, br3, bw', hsplit2, hbw3, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw2) (bits := bitsTot >>> 2) (len := lenTot - 2)
        hbit2 hcur2 (by omega))
  have hshift3 : bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 2 >>> 1 := by simp [hshift2]
      _ = bitsTot >>> 3 := by simpa using (Nat.shiftRight_add bitsTot 2 1)
  have hbw4 : Png.BitWriter.writeBit bw3 ((bitsTot >>> 3) % 2) = bw4 := by
    simp [bw3, bw4, Png.BitWriter.writeBits, hshift3]
  have hread3 : br3.readBit = ((bitsTot >>> 3) % 2, br4) := by
    simpa [br3, br4, bw', hsplit3, hbw4, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw3) (bits := bitsTot >>> 3) (len := lenTot - 3)
        hbit3 hcur3 (by omega))
  have hshift4 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 >>> 1 := by simp [hshift3]
      _ = bitsTot >>> 4 := by simpa using (Nat.shiftRight_add bitsTot 3 1)
  have hbw5 : Png.BitWriter.writeBit bw4 ((bitsTot >>> 4) % 2) = bw5 := by
    simp [bw4, bw5, Png.BitWriter.writeBits, hshift4]
  have hread4 : br4.readBit = ((bitsTot >>> 4) % 2, br5) := by
    simpa [br4, br5, bw', hsplit4, hbw5, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw4) (bits := bitsTot >>> 4) (len := lenTot - 4)
        hbit4 hcur4 (by omega))
  have hprefix2 :
      bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) = bitsTot % 2 ^ 2 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 1).symm
  have hprefix3 :
      bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) = bitsTot % 2 ^ 3 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 2).symm
  have hprefix4 :
      bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) = bitsTot % 2 ^ 4 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 3).symm
  have hprefix5 :
      bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) = bitsTot % 2 ^ 5 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 4).symm
  have htable1 : 1 < generatedDynamicDistTableLz77.table.size := by
    rw [generatedDynamicDistTableLz77_table_size]
    decide
  have htable2 : 2 < generatedDynamicDistTableLz77.table.size := by
    rw [generatedDynamicDistTableLz77_table_size]
    decide
  have htable3 : 3 < generatedDynamicDistTableLz77.table.size := by
    rw [generatedDynamicDistTableLz77_table_size]
    decide
  have htable4 : 4 < generatedDynamicDistTableLz77.table.size := by
    rw [generatedDynamicDistTableLz77_table_size]
    decide
  have htable5 : 5 < generatedDynamicDistTableLz77.table.size := by
    rw [generatedDynamicDistTableLz77_table_size]
    decide
  have hcode1 : bitsTot % 2 <
      (Array.getInternal generatedDynamicDistTableLz77.table 1 htable1).size :=
    generatedDynamicDistTableLz77_prefix_code_lt_row_size bitsTot 1
      (by decide) (by decide) htable1
  have hcode2 : bitsTot % 2 ^ 2 <
      (Array.getInternal generatedDynamicDistTableLz77.table 2 htable2).size :=
    generatedDynamicDistTableLz77_prefix_code_lt_row_size bitsTot 2
      (by decide) (by decide) htable2
  have hcode3 : bitsTot % 2 ^ 3 <
      (Array.getInternal generatedDynamicDistTableLz77.table 3 htable3).size :=
    generatedDynamicDistTableLz77_prefix_code_lt_row_size bitsTot 3
      (by decide) (by decide) htable3
  have hcode4 : bitsTot % 2 ^ 4 <
      (Array.getInternal generatedDynamicDistTableLz77.table 4 htable4).size :=
    generatedDynamicDistTableLz77_prefix_code_lt_row_size bitsTot 4
      (by decide) (by decide) htable4
  have hcode5 : bitsTot % 2 ^ 5 <
      (Array.getInternal generatedDynamicDistTableLz77.table 5 htable5).size :=
    generatedDynamicDistTableLz77_prefix5_code_lt_row_size bitsTot htable5
  have hrow1 :
      Array.getInternal (Array.getInternal generatedDynamicDistTableLz77.table 1 htable1)
        (bitsTot % 2) hcode1 = none :=
    generatedDynamicDistTableLz77_prefix_row_none_internal bitsTot 1
      (by decide) (by decide) htable1 hcode1
  have hrow2 :
      Array.getInternal (Array.getInternal generatedDynamicDistTableLz77.table 2 htable2)
        (bitsTot % 2 ^ 2) hcode2 = none :=
    generatedDynamicDistTableLz77_prefix_row_none_internal bitsTot 2
      (by decide) (by decide) htable2 hcode2
  have hrow3 :
      Array.getInternal (Array.getInternal generatedDynamicDistTableLz77.table 3 htable3)
        (bitsTot % 2 ^ 3) hcode3 = none :=
    generatedDynamicDistTableLz77_prefix_row_none_internal bitsTot 3
      (by decide) (by decide) htable3 hcode3
  have hrow4 :
      Array.getInternal (Array.getInternal generatedDynamicDistTableLz77.table 4 htable4)
        (bitsTot % 2 ^ 4) hcode4 = none :=
    generatedDynamicDistTableLz77_prefix_row_none_internal bitsTot 4
      (by decide) (by decide) htable4 hcode4
  have hrow5' :
      Array.getInternal (Array.getInternal generatedDynamicDistTableLz77.table 5 htable5)
        (bitsTot % 2 ^ 5) hcode5 = some sym :=
    generatedDynamicDistTableLz77_prefix5_row_some_internal
      bitsTot sym hrow5 htable5 hcode5
  have hbr0 : br0.bytePos < br0.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hbr4 : br4.bytePos < br4.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br4 (by omega)
  have hstep0 :
      generatedDynamicDistTableLz77.decode br0 =
        Png.Huffman.decodeFuel generatedDynamicDistTableLz77 4 (bitsTot % 2) 1 br1 := by
    have hcode1' :
        0 ||| ((bitsTot % 2) <<< 0) <
          (Array.getInternal generatedDynamicDistTableLz77.table 1 htable1).size := by
      simpa using hcode1
    have hrow1' :
        Array.getInternal
          (Array.getInternal generatedDynamicDistTableLz77.table 1 htable1)
          (0 ||| ((bitsTot % 2) <<< 0)) hcode1' = none := by
      simpa using hrow1
    unfold Png.Huffman.decode
    rw [generatedDynamicDistTableLz77_maxLen]
    simpa [hread0] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicDistTableLz77)
        (fuel := 4) (code := 0) (len := 0) (br := br0) (br' := br1)
        (bit := bitsTot % 2) (hbyte := hbr0) (hread := hread0)
        (htable := htable1) (hcode := hcode1') (hrow := hrow1'))
  have hstep1 :
      Png.Huffman.decodeFuel generatedDynamicDistTableLz77 4 (bitsTot % 2) 1 br1 =
        Png.Huffman.decodeFuel generatedDynamicDistTableLz77 3 (bitsTot % 2 ^ 2) 2 br2 := by
    have hcode' :
        bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) <
          (Array.getInternal generatedDynamicDistTableLz77.table 2 htable2).size := by
      simpa [hprefix2] using hcode2
    have hrow'' :
        Array.getInternal
          (Array.getInternal generatedDynamicDistTableLz77.table 2 htable2)
          (bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1)) hcode' = none := by
      simpa [hprefix2] using hrow2
    simpa [hprefix2] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicDistTableLz77)
        (fuel := 3) (code := bitsTot % 2) (len := 1)
        (br := br1) (br' := br2) (bit := (bitsTot >>> 1) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega))
        (hread := hread1) (htable := htable2) (hcode := hcode') (hrow := hrow''))
  have hstep2 :
      Png.Huffman.decodeFuel generatedDynamicDistTableLz77 3 (bitsTot % 2 ^ 2) 2 br2 =
        Png.Huffman.decodeFuel generatedDynamicDistTableLz77 2 (bitsTot % 2 ^ 3) 3 br3 := by
    have hcode' :
        bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) <
          (Array.getInternal generatedDynamicDistTableLz77.table 3 htable3).size := by
      simpa [hprefix3] using hcode3
    have hrow'' :
        Array.getInternal
          (Array.getInternal generatedDynamicDistTableLz77.table 3 htable3)
          (bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2)) hcode' = none := by
      simpa [hprefix3] using hrow3
    simpa [hprefix3] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicDistTableLz77)
        (fuel := 2) (code := bitsTot % 2 ^ 2) (len := 2)
        (br := br2) (br' := br3) (bit := (bitsTot >>> 2) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br2 (by omega))
        (hread := hread2) (htable := htable3) (hcode := hcode') (hrow := hrow''))
  have hstep3 :
      Png.Huffman.decodeFuel generatedDynamicDistTableLz77 2 (bitsTot % 2 ^ 3) 3 br3 =
        Png.Huffman.decodeFuel generatedDynamicDistTableLz77 1 (bitsTot % 2 ^ 4) 4 br4 := by
    have hcode' :
        bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) <
          (Array.getInternal generatedDynamicDistTableLz77.table 4 htable4).size := by
      simpa [hprefix4] using hcode4
    have hrow'' :
        Array.getInternal
          (Array.getInternal generatedDynamicDistTableLz77.table 4 htable4)
          (bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3)) hcode' = none := by
      simpa [hprefix4] using hrow4
    simpa [hprefix4] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicDistTableLz77)
        (fuel := 1) (code := bitsTot % 2 ^ 3) (len := 3)
        (br := br3) (br' := br4) (bit := (bitsTot >>> 3) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br3 (by omega))
        (hread := hread3) (htable := htable4) (hcode := hcode') (hrow := hrow''))
  have hstep4 :
      Png.Huffman.decodeFuel generatedDynamicDistTableLz77 1
          (bitsTot % 2 ^ 4) 4 br4 =
        some (sym, br5) := by
    have hcode' :
        bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) <
          (Array.getInternal generatedDynamicDistTableLz77.table 5 htable5).size := by
      simpa [hprefix5] using hcode5
    have hrow'' :
        Array.getInternal
          (Array.getInternal generatedDynamicDistTableLz77.table 5 htable5)
          (bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4)) hcode' = some sym := by
      simpa [hprefix5] using hrow5'
    simpa [hprefix5] using
      (Png.Huffman.decodeFuel_step_some (h := generatedDynamicDistTableLz77)
        (fuel := 0) (code := bitsTot % 2 ^ 4) (len := 4)
        (br := br4) (br' := br5) (bit := (bitsTot >>> 4) % 2)
        (sym := sym) (hbyte := hbr4) (hread := hread4)
        (htable := htable5) (hcode := hcode') (hrow := hrow''))
  calc
    generatedDynamicDistTableLz77.decode br0 =
        Png.Huffman.decodeFuel generatedDynamicDistTableLz77 4
          (bitsTot % 2) 1 br1 := hstep0
    _ = Png.Huffman.decodeFuel generatedDynamicDistTableLz77 3
          (bitsTot % 2 ^ 2) 2 br2 := hstep1
    _ = Png.Huffman.decodeFuel generatedDynamicDistTableLz77 2
          (bitsTot % 2 ^ 3) 3 br3 := hstep2
    _ = Png.Huffman.decodeFuel generatedDynamicDistTableLz77 1
          (bitsTot % 2 ^ 4) 4 br4 := hstep3
    _ = some (sym, br5) := hstep4

/-- A generated LZ77 dynamic distance code decodes to its distance symbol from
the same writer-built payload stream. -/
lemma generatedDynamicDistTableLz77_decode_symbol_readerAt_writeBits
    (freqs : Array Nat) (sym : Nat)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (hsym : sym < (Png.generatedDynamicDistLengthsLz77 freqs).size)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths := Png.generatedDynamicDistLengthsLz77 freqs
    let codes := Png.canonicalRevCodesFromLengths lengths
    let bitsTot := codes[sym]!.1 ||| (restBits <<< 5)
    let lenTot := 5 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br5 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    generatedDynamicDistTableLz77.decode br0 = some (sym, br5) := by
  intro lengths codes bitsTot lenTot bw' br0 br5
  have hrow5 :
      generatedDynamicDistTableLz77.table[5]![bitsTot % 2 ^ 5]! =
        some sym := by
    simpa [lengths, codes, bitsTot] using
      generatedDynamicDistTableLz77_prefix5_row_some freqs sym restBits hsym
  simpa [bitsTot, lenTot, bw', br0, br5] using
    generatedDynamicDistTableLz77_decode_readerAt_writeBits_core
      bw bitsTot restLen sym hrow5 hbit hcur

/-- The generated LZ77 dynamic table spec packages the exact literal/length and
distance Huffman tables reconstructed from the generated header. -/
def generatedDynamicTableSpecLz77
    (source : Array Png.Lz77Token) : Png.DynamicTableSpec :=
  let litLenLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  { litLenLengths := litLenLengths
    distLengths := distLengths
    litLenTable := generatedDynamicLitLenTableLz77 source
    distTable := generatedDynamicDistTableLz77 }

/-- Validating the generated LZ77 length arrays yields the named generated
dynamic table spec. This is the parser boundary bridge for LZ77 blocks. -/
lemma generatedDynamicTableSpecLz77_ofLengths?_eq_named
    (source : Array Png.Lz77Token) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    Png.DynamicTableSpec.ofLengths? litLenLengths distLengths =
      some (generatedDynamicTableSpecLz77 source) := by
  intro litLenLengths distLengths
  have hlit :
      Png.mkHuffman litLenLengths =
        some (generatedDynamicLitLenTableLz77 source) := by
    simpa [litLenLengths] using
      mkHuffman_generatedDynamicLitLenLengthsLz77_eq source
  have hdist :
      Png.buildDynamicDistTable distLengths =
        some generatedDynamicDistTableLz77 := by
    simpa [distLengths] using
      buildDynamicDistTable_generatedDynamicDistLengthsLz77_eq
        (Png.distSymbolFreqsLz77 source)
  simpa [generatedDynamicTableSpecLz77, litLenLengths, distLengths] using
    Png.DynamicTableSpec.ofLengths?_mk (hlit := hlit) (hdist := hdist)

/-- Generated LZ77 EOB codes have the uniform nine-bit literal/length width.
This converts generated code tables into the payload bit length used for EOB. -/
lemma generatedDynamicLitLenCodesLz77_eob_len_eq_nine
    (source : Array Png.Lz77Token) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let codes := Png.canonicalRevCodesFromLengths lengths
    codes[256]!.2 = 9 := by
  intro lengths codes
  have hsym : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengthsLz77_eob_inBounds source
  have hpos : 0 < lengths[256]! := by
    have hposChecked :=
      generatedDynamicLitLenLengthsLz77_eob_pos source
    simpa [lengths, getElem!_pos lengths 256 hsym] using hposChecked
  have hcodeLen :=
    canonicalRevCodesFromLengths_get!_snd_of_pos lengths 256 hsym hpos
  have hentry : lengths[256]! = 9 := by
    have heq := generatedDynamicLitLenLengthsLz77_eob_eq_nine source
    simpa [lengths, getElem!_pos lengths 256 hsym] using heq
  simpa [codes, hentry] using hcodeLen

/-- The generated LZ77 EOB payload bit length is nine bits. This matches the
generated literal/length table decode replay. -/
lemma dynamicPayloadLz77EobBitLen_generated_eq_nine
    (source : Array Png.Lz77Token) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    dynamicPayloadLz77EobBitLen litLenCodes = 9 := by
  intro litLenCodes
  simpa [dynamicPayloadLz77EobBitLen, litLenCodes] using
    generatedDynamicLitLenCodesLz77_eob_len_eq_nine source

/-- Generated LZ77 literal codes have the uniform nine-bit literal/length width
at each literal token emitted by the source stream. -/
lemma generatedDynamicLitLenCodesLz77_literal_len_eq_nine_at
    (source : Array Png.Lz77Token) (target : Nat) (b : UInt8)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.literal b) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let codes := Png.canonicalRevCodesFromLengths lengths
    codes[b.toNat]!.2 = 9 := by
  intro lengths codes
  have hsym : b.toNat < lengths.size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size,
        litLenSymbolFreqsLz77_size]
    omega
  have hpos : 0 < lengths[b.toNat]! := by
    simpa [lengths] using
      generatedDynamicLitLenLengthsLz77_literal_pos_at
        source target b htarget ht
  have hcodeLen :=
    canonicalRevCodesFromLengths_get!_snd_of_pos lengths b.toNat hsym hpos
  have hnine :
      lengths[b.toNat]! = 9 := by
    have hposChecked : 0 < lengths[b.toNat] := by
      simpa [getElem!_pos lengths b.toNat hsym] using hpos
    have hiff :=
      generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
        (Png.litLenSymbolFreqsLz77 source) b.toNat hsym
    have hchecked := hiff.mp hposChecked
    simpa [getElem!_pos lengths b.toNat hsym] using hchecked
  simpa [codes, hnine] using hcodeLen

/-- A generated LZ77 literal payload token has nine literal/length bits. This
specializes the token bit-length view to literal transitions. -/
lemma dynamicPayloadLz77TokenBitLen_generated_literal_eq_nine_at
    (source : Array Png.Lz77Token) (target : Nat) (b : UInt8)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.literal b) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    dynamicPayloadLz77TokenBitLen litLenCodes distCodes
      (Png.Lz77Token.literal b) = 9 := by
  intro litLenCodes distCodes
  simpa [dynamicPayloadLz77TokenBitLen, litLenCodes, distCodes] using
    generatedDynamicLitLenCodesLz77_literal_len_eq_nine_at
      source target b htarget ht

/-- Generated LZ77 match codes have the uniform nine-bit literal/length width
at each match token emitted by the source stream. -/
lemma generatedDynamicLitLenCodesLz77_match_len_eq_nine_at
    (source : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let codes := Png.canonicalRevCodesFromLengths lengths
    codes[(Png.deflateLengthInfo len).1]!.2 = 9 := by
  intro lengths codes
  let sym := (Png.deflateLengthInfo len).1
  have hsym : sym < lengths.size := by
    have hsym' := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size,
        litLenSymbolFreqsLz77_size]
    have hsym'' : sym < 286 := by
      simpa [sym, Png.deflateLengthInfo] using hsym'
    omega
  have hpos : 0 < lengths[sym]! := by
    simpa [lengths, sym] using
      generatedDynamicLitLenLengthsLz77_match_pos_at
        source target len distance htarget ht hlen
  have hcodeLen :=
    canonicalRevCodesFromLengths_get!_snd_of_pos lengths sym hsym hpos
  have hnine :
      lengths[sym]! = 9 := by
    have hposChecked : 0 < lengths[sym] := by
      simpa [getElem!_pos lengths sym hsym] using hpos
    have hiff :=
      generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
        (Png.litLenSymbolFreqsLz77 source) sym hsym
    have hchecked := hiff.mp hposChecked
    simpa [getElem!_pos lengths sym hsym] using hchecked
  simpa [codes, sym, hnine] using hcodeLen

/-- Generated LZ77 match literal/length code bits fit in the uniform nine-bit
width. Match transition proofs use this to peel the first field off the
writer-built payload stream. -/
lemma generatedDynamicLitLenCodesLz77_match_bits_lt_codeSpace_at
    (source : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let codes := Png.canonicalRevCodesFromLengths lengths
    codes[(Png.deflateLengthInfo len).1]!.1 < 2 ^ 9 := by
  intro lengths codes
  let sym := (Png.deflateLengthInfo len).1
  have hsym : sym < lengths.size := by
    have hsym' := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size,
        litLenSymbolFreqsLz77_size]
    have hsym'' : sym < 286 := by
      simpa [sym, Png.deflateLengthInfo] using hsym'
    omega
  have hpos : 0 < lengths[sym]! := by
    simpa [lengths, sym] using
      generatedDynamicLitLenLengthsLz77_match_pos_at
        source target len distance htarget ht hlen
  have hbits :=
    canonicalRevCodesFromLengths_get!_fst_lt_pow_snd_of_pos
      lengths sym hsym hpos
  have hlen9 :
      codes[sym]!.2 = 9 := by
    simpa [lengths, codes, sym] using
      generatedDynamicLitLenCodesLz77_match_len_eq_nine_at
        source target len distance htarget ht hlen
  simpa [codes, sym, hlen9] using hbits

/-- A generated LZ77 match payload token has the expected dynamic payload
width: nine literal/length bits, length extra bits, a five-bit distance code,
and distance extra bits. -/
lemma dynamicPayloadLz77TokenBitLen_generated_match_eq
    (source : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258)
    {sym extraBits extraLen distSym distExtraBits distExtraLen : Nat}
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen)) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    dynamicPayloadLz77TokenBitLen litLenCodes distCodes
      (Png.Lz77Token.match len distance) =
        9 + extraLen + 5 + distExtraLen := by
  intro litLenCodes distCodes
  have hlitLen :
      litLenCodes[sym]!.2 = 9 := by
    have h :=
      generatedDynamicLitLenCodesLz77_match_len_eq_nine_at
        source target len distance htarget ht hlen
    simpa [litLenCodes, hlenInfo] using h
  have hdistSpec :=
    Png.deflateDistanceInfo_decodeDistance_correct hdistInfo
  rcases hdistSpec with ⟨hdistSym, _hdistExtra, _hextraDist, _hbase, _hbits⟩
  have hdistSymLen :
      distSym <
        (Png.generatedDynamicDistLengthsLz77
          (Png.distSymbolFreqsLz77 source)).size := by
    have hsize :
        (Png.generatedDynamicDistLengthsLz77
          (Png.distSymbolFreqsLz77 source)).size = 30 := by
      simpa using
        generatedDynamicDistLengthsLz77_size
          (Png.distSymbolFreqsLz77 source)
    have hbaseSize : Png.distBases.size = 30 := by decide
    omega
  have hdistLen :
      distCodes[distSym]!.2 = 5 := by
    simpa [distCodes] using
      generatedDynamicDistCodesLz77_len_eq_five
        (Png.distSymbolFreqsLz77 source) distSym hdistSymLen
  simpa [dynamicPayloadLz77TokenBitLen, hlenInfo, hdistInfo, litLenCodes,
    distCodes, hlitLen, hdistLen, Nat.add_assoc]

/-- The length-extra field emitted for an LZ77 match decodes back to the match
length and advances the reader past exactly those extra bits. -/
lemma generatedDynamicPayloadLz77Match_decodeLength_readerAt_writeBits
    (bw : Png.BitWriter)
    (len sym extraBits extraLen restBits restLen : Nat)
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hlen : 3 ≤ len ∧ len ≤ 258)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := extraBits ||| (restBits <<< extraLen)
    let lenTot := extraLen + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br' := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot extraLen) bw'.flush
      (by
        have hk : extraLen ≤ lenTot := by omega
        simpa [lenTot] using
          Png.flush_size_writeBits_prefix bw bitsTot extraLen lenTot hk)
      (Png.bitPos_lt_8_writeBits bw bitsTot extraLen hbit)
    ∃ hsym hbits, Png.decodeLength sym br hsym hbits = (len, br') := by
  intro bitsTot lenTot bw' br br'
  rcases Png.deflateLengthInfo_decodeLength_correct hlenInfo hlen.1 hlen.2 with
    ⟨hsym, hidxBase, hidxExtra, hextra, hbase, hbitsLt⟩
  refine ⟨hsym, ?_, ?_⟩
  · have hread :=
      Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot)
        (len := lenTot) (k := extraLen) (hk := by omega) hbit
    have hcanon :
        Png.lengthExtra[sym - 257]'(by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : Png.lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) = extraLen := by
      calc
        Png.lengthExtra[sym - 257]'(by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : Png.lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) =
            Array.getInternal Png.lengthExtra (sym - 257)
              (by
                have hidxle : sym - 257 ≤ 28 := by omega
                have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                have hsize : Png.lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt) := rfl
        _ = Array.getInternal Png.lengthExtra (sym - 257) hidxExtra := by
              congr
        _ = extraLen := by simpa using hextra.symm
    simpa [br, bw', lenTot, hcanon] using hread
  · have hdecode :=
      Png.decodeLength_readerAt_writeBits_prefix (bw := bw) (sym := sym)
        (extraBits := extraBits) (extraLen := extraLen)
        (restBits := restBits) (restLen := restLen) (lenOut := len)
        (hsym := hsym) (hidxBase := hidxBase) (hidxExtra := hidxExtra)
        (hextra := hextra) (hbase := hbase) (hbitsLt := hbitsLt)
        (hbit := hbit) (hcur := hcur)
    simpa [bitsTot, lenTot, bw', br, br'] using hdecode

/-- The distance-extra field emitted for an LZ77 match decodes back to the
match distance and advances the reader past exactly those extra bits. -/
lemma generatedDynamicPayloadLz77Match_decodeDistance_readerAt_writeBits
    (bw : Png.BitWriter)
    (distance distSym distExtraBits distExtraLen restBits restLen : Nat)
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := distExtraBits ||| (restBits <<< distExtraLen)
    let lenTot := distExtraLen + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br' := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot distExtraLen) bw'.flush
      (by
        have hk : distExtraLen ≤ lenTot := by omega
        simpa [lenTot] using
          Png.flush_size_writeBits_prefix bw bitsTot distExtraLen lenTot hk)
      (Png.bitPos_lt_8_writeBits bw bitsTot distExtraLen hbit)
    ∃ hdist hbits,
      Png.decodeDistance distSym br hdist hbits = (distance, br') := by
  intro bitsTot lenTot bw' br br'
  rcases Png.deflateDistanceInfo_decodeDistance_correct hdistInfo with
    ⟨hdist, hdistExtra, hextra, hbase, hbitsLt⟩
  refine ⟨hdist, ?_, ?_⟩
  · have hread :=
      Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot)
        (len := lenTot) (k := distExtraLen) (hk := by omega) hbit
    have hcanon :
        Png.distExtra[distSym]'(by
          have hDistExtraSize : Png.distExtra.size = 30 := by decide
          have hDistBasesSize : Png.distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist) = distExtraLen := by
      calc
        Png.distExtra[distSym]'(by
          have hDistExtraSize : Png.distExtra.size = 30 := by decide
          have hDistBasesSize : Png.distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist) =
            Array.getInternal Png.distExtra distSym
              (by
                have hDistExtraSize : Png.distExtra.size = 30 := by decide
                have hDistBasesSize : Png.distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist) := rfl
        _ = Array.getInternal Png.distExtra distSym hdistExtra := by
              congr
        _ = distExtraLen := by simpa using hextra.symm
    simpa [br, bw', lenTot, hcanon] using hread
  · have hdecode :=
      Png.decodeDistance_readerAt_writeBits_prefix (bw := bw) (sym := distSym)
        (extraBits := distExtraBits) (extraLen := distExtraLen)
        (restBits := restBits) (restLen := restLen) (distance := distance)
        (hdist := hdist) (hdistExtra := hdistExtra) (hextra := hextra)
        (hbase := hbase) (hbitsLt := hbitsLt)
        (hbit := hbit) (hcur := hcur)
    simpa [bitsTot, lenTot, bw', br, br'] using hdecode

/-- Packages arbitrary-distance generated dynamic match decodes into the
generic dynamic-payload copy transition. This separates semantic validity from
the bitstream reader arithmetic. -/
lemma dynamicPayloadTransition_lz77_copy_of_decodes
    (spec : Png.DynamicTableSpec)
    (br0 br1 br2 br3 br4 : Png.BitReader)
    (out out' : ByteArray)
    (len distance sym extraBits extraLen distSym distExtraBits distExtraLen : Nat)
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (hlen : 3 ≤ len ∧ len ≤ 258)
    (hdecodeSym : spec.litLenTable.decode br0 = some (sym, br1))
    (hdecodeLenEx :
      ∃ hsym hbits,
        Png.decodeLength sym br1 hsym hbits = (len, br2))
    (hdecodeDistSym : spec.distTable.decode br2 = some (distSym, br3))
    (hdecodeDistEx :
      ∃ hdist hbitsD,
        Png.decodeDistance distSym br3 hdist hbitsD = (distance, br4))
    (hcopy : Png.copyDistance out distance len = some out') :
    Png.DynamicPayloadTransition spec br0 out br4 out' := by
  rcases hdecodeLenEx with ⟨hsymLen, hbitsLen, hdecodeLen⟩
  rcases hdecodeDistEx with ⟨hdistDecode, hbitsD, hdecodeDist⟩
  rcases Png.deflateLengthInfo_decodeLength_correct hlenInfo hlen.1 hlen.2 with
    ⟨_hsymInfo, _hidxBase, hidxExtra, hextraLen, _hbaseLen, _hbitsLenLt⟩
  rcases Png.deflateDistanceInfo_decodeDistance_correct hdistInfo with
    ⟨hdist, hdistExtra, hextraDist, _hbaseDist, _hbitsDistLt⟩
  have hnotLit : ¬ sym < 256 := by
    have hs := hsymLen
    omega
  have hnotEob : (sym == 256) = false := by
    cases hbeq : (sym == 256) with
    | false => simpa using hbeq
    | true =>
        have hs : sym = 256 := by simpa using hbeq
        omega
  have hextra :
      extraLen =
        Array.getInternal Png.lengthExtra (sym - 257) (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : Png.lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) := by
    calc
      extraLen = Array.getInternal Png.lengthExtra (sym - 257) hidxExtra := hextraLen
      _ = Array.getInternal Png.lengthExtra (sym - 257) (by
            have hidxle : sym - 257 ≤ 28 := by omega
            have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
            have hsize : Png.lengthExtra.size = 29 := by decide
            simpa [hsize] using hidxlt) := by
          congr
  have hextraD :
      distExtraLen =
        Array.getInternal Png.distExtra distSym (by
          have hDistExtraSize : Png.distExtra.size = 30 := by decide
          have hDistBasesSize : Png.distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist) := by
    calc
      distExtraLen = Array.getInternal Png.distExtra distSym hdistExtra := hextraDist
      _ = Array.getInternal Png.distExtra distSym (by
            have hDistExtraSize : Png.distExtra.size = 30 := by decide
            have hDistBasesSize : Png.distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist) := by
          congr
  exact Png.DynamicPayloadTransition.copy
    (spec := spec) (br := br0) (out := out)
    (sym := sym) (extra := extraLen) (len := len)
    (distSym := distSym) (extraD := distExtraLen) (distance := distance)
    (br' := br1) (br'' := br2) (br''' := br3)
    (br'''' := br4) (out' := out')
    hdecodeSym hnotLit hnotEob hsymLen hextra
    (by simpa [hextra] using hbitsLen)
    (by simpa using hdecodeLen)
    hdecodeDistSym hdist hextraD
    (by simpa [hextraD] using hbitsD)
    (by simpa using hdecodeDist)
    hcopy

/-- The generated LZ77 payload EOB code produces a terminal dynamic-payload
finish step through the generated LZ77 literal/length table. -/
lemma generatedDynamicPayloadLz77Eob_finish_readerAt_writeBits
    (source : Array Png.Lz77Token) (bw : Png.BitWriter)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpecLz77 source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let bits := dynamicPayloadLz77EobBits litLenCodes
    let len := dynamicPayloadLz77EobBitLen litLenCodes
    let bw' := Png.BitWriter.writeBits bw bits len
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bits len) hbit
    let br' := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bits len)
      bw'.flush
      (by
        simpa [bw'] using
          (le_rfl : (Png.BitWriter.writeBits bw bits len).flush.size ≤
            (Png.BitWriter.writeBits bw bits len).flush.size))
      (Png.bitPos_lt_8_writeBits bw bits len hbit)
    Png.DynamicPayloadFinish spec br0 out br' := by
  intro spec litLenCodes bits len bw' br0 br'
  have hlen : len = 9 := by
    simpa [len, litLenCodes] using
      dynamicPayloadLz77EobBitLen_generated_eq_nine source
  have hdecode :
      (generatedDynamicLitLenTableLz77 source).decode br0 =
        some (256, br') := by
    have h :=
      generatedDynamicLitLenTableLz77_decode_eob_readerAt_writeBits
        source bw 0 0 hbit hcur
    simpa [br0, br', bw', bits, len, litLenCodes, dynamicPayloadLz77EobBits,
      hlen] using h
  exact Png.DynamicPayloadFinish.eob
    (spec := spec) (br := br0) (out := out)
    (sym := 256) (br' := br') (by simpa [spec, generatedDynamicTableSpecLz77] using hdecode)
    (by decide) (by decide)

/-- A generated LZ77 literal payload token produces one validated dynamic
payload literal transition through the generated LZ77 table spec. -/
lemma generatedDynamicPayloadLz77Literal_transition_readerAt_writeBits
    (source : Array Png.Lz77Token) (target : Nat) (b : UInt8)
    (bw : Png.BitWriter) (out : ByteArray) (tailBits tailLen : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.literal b)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpecLz77 source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    let bits := dynamicPayloadLz77TokenBits litLenCodes distCodes
      (Png.Lz77Token.literal b)
    let len := dynamicPayloadLz77TokenBitLen litLenCodes distCodes
      (Png.Lz77Token.literal b)
    let bitsTot := bits ||| (tailBits <<< len)
    let lenTot := len + tailLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br' := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot len)
      bw'.flush
      (by
        have hk : len ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot len lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot len hbit)
    Png.DynamicPayloadTransition spec br0 out br'
      (out.push (Png.u8 b.toNat)) := by
  intro spec litLenCodes distCodes bits len bitsTot lenTot bw' br0 br'
  have hlen : len = 9 := by
    simpa [len, litLenCodes, distCodes] using
      dynamicPayloadLz77TokenBitLen_generated_literal_eq_nine_at
        source target b htarget ht
  have hdecode :
      (generatedDynamicLitLenTableLz77 source).decode br0 =
        some (b.toNat, br') := by
    have h :=
      generatedDynamicLitLenTableLz77_decode_literal_at_readerAt_writeBits
        source target b bw tailBits tailLen htarget ht hbit hcur
    simpa [br0, br', bw', bits, len, bitsTot, lenTot, litLenCodes,
      distCodes, dynamicPayloadLz77TokenBits, hlen] using h
  have hsym : b.toNat < 256 := UInt8.toNat_lt b
  exact Png.DynamicPayloadTransition.literal
    (spec := spec) (br := br0) (out := out)
    (sym := b.toNat) (br' := br') (by simpa [spec, generatedDynamicTableSpecLz77] using hdecode)
    hsym

/-- Generated dynamic LZ77 match token lengths normalize to the field layout
used by decoder replay: literal/length code, length extras, distance code,
distance extras, then the remaining payload tail. -/
lemma dynamicPayloadLz77TokenBitLen_generated_match_tail_eq
    (source : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258)
    {sym extraBits extraLen distSym distExtraBits distExtraLen : Nat}
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (tailLen : Nat) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    dynamicPayloadLz77TokenBitLen litLenCodes distCodes
        (Png.Lz77Token.match len distance) + tailLen =
      9 + (extraLen + (5 + (distExtraLen + tailLen))) := by
  intro litLenCodes distCodes
  have htoken :=
    dynamicPayloadLz77TokenBitLen_generated_match_eq
      source target len distance htarget ht hlen hlenInfo hdistInfo
  have htoken' :
      dynamicPayloadLz77TokenBitLen litLenCodes distCodes
          (Png.Lz77Token.match len distance) =
        9 + extraLen + 5 + distExtraLen := by
    simpa [litLenCodes, distCodes] using htoken
  omega

/-- Generated dynamic LZ77 match token bits normalize to the field layout used
by the decoder replay lemmas, with an arbitrary payload tail appended. -/
lemma dynamicPayloadLz77TokenBits_generated_match_tail_eq
    (source : Array Png.Lz77Token) (target len distance : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlen : 3 ≤ len ∧ len ≤ 258)
    {sym extraBits extraLen distSym distExtraBits distExtraLen : Nat}
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (tailBits : Nat) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    let tokenBits :=
      dynamicPayloadLz77TokenBits litLenCodes distCodes
        (Png.Lz77Token.match len distance)
    let tokenLen :=
      dynamicPayloadLz77TokenBitLen litLenCodes distCodes
        (Png.Lz77Token.match len distance)
    let distExtraTailBits := distExtraBits ||| (tailBits <<< distExtraLen)
    let distTailBits := distCodes[distSym]!.1 ||| (distExtraTailBits <<< 5)
    let lenTailBits := extraBits ||| (distTailBits <<< extraLen)
    tokenBits ||| (tailBits <<< tokenLen) =
      litLenCodes[sym]!.1 ||| (lenTailBits <<< 9) := by
  intro litLenCodes distCodes tokenBits tokenLen distExtraTailBits
    distTailBits lenTailBits
  rcases Png.deflateDistanceInfo_decodeDistance_correct hdistInfo with
    ⟨hdistSym, _hdistExtra, _hextraDist, _hbaseDist, _hbitsDistLt⟩
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  have hdistSymLen : distSym < distLengths.size := by
    have hsize : distLengths.size = 30 := by
      simpa [distLengths] using
        generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
    have hbaseSize : Png.distBases.size = 30 := by decide
    omega
  have hdistLen :
      distCodes[distSym]!.2 = 5 := by
    simpa [distCodes, distLengths] using
      generatedDynamicDistCodesLz77_len_eq_five
        (Png.distSymbolFreqsLz77 source) distSym hdistSymLen
  have hlitLen :
      litLenCodes[sym]!.2 = 9 := by
    have h :=
      generatedDynamicLitLenCodesLz77_match_len_eq_nine_at
        source target len distance htarget ht hlen
    simpa [litLenCodes, hlenInfo] using h
  simp [tokenBits, tokenLen, dynamicPayloadLz77TokenBits,
    dynamicPayloadLz77TokenBitLen, hlenInfo, hdistInfo, hlitLen, hdistLen,
    distExtraTailBits, distTailBits, lenTailBits, Nat.or_assoc,
    Nat.shiftLeft_or_distrib, Png.shiftLeft_shiftLeft, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

set_option maxRecDepth 250000 in
set_option maxHeartbeats 5000000 in
/-- Field-by-field replay for one generated dynamic LZ77 match token. This is
the compact transition lemma used before rewriting from public packed token
bits. -/
lemma generatedDynamicPayloadLz77Match_manual_transition_readerAt_writeBits
    (source : Array Png.Lz77Token) (target : Nat)
    (bw : Png.BitWriter) (out out' : ByteArray)
    (len distance sym extraBits extraLen distSym distExtraBits distExtraLen : Nat)
    (tailBits tailLen : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (hexpand : Png.lz77TokenExpand? out (.match len distance) = some out')
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpecLz77 source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    let litBits := litLenCodes[sym]!.1
    let distBits := distCodes[distSym]!.1
    let distExtraTailBits := distExtraBits ||| (tailBits <<< distExtraLen)
    let distExtraTailLen := distExtraLen + tailLen
    let distTailBits := distBits ||| (distExtraTailBits <<< 5)
    let distTailLen := 5 + distExtraTailLen
    let lenTailBits := extraBits ||| (distTailBits <<< extraLen)
    let lenTailLen := extraLen + distTailLen
    let bitsTot := litBits ||| (lenTailBits <<< 9)
    let lenTot := 9 + lenTailLen
    let bwLenStart := Png.BitWriter.writeBits bw bitsTot 9
    let bwDistStart := Png.BitWriter.writeBits bwLenStart lenTailBits extraLen
    let bwDistExtraStart := Png.BitWriter.writeBits bwDistStart distTailBits 5
    let bwAll := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits distExtraLen)
      (Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits
        distExtraTailLen).flush
      (by
        have hk : distExtraLen ≤ distExtraTailLen := by
          simp [distExtraTailLen]
        exact Png.flush_size_writeBits_prefix bwDistExtraStart
          distExtraTailBits distExtraLen distExtraTailLen hk)
      (Png.bitPos_lt_8_writeBits bwDistExtraStart distExtraTailBits
        distExtraLen
        (Png.bitPos_lt_8_writeBits bwDistStart distTailBits 5
          (Png.bitPos_lt_8_writeBits bwLenStart lenTailBits extraLen
            (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit))))
    Png.DynamicPayloadTransition spec br0 out brAfter out' := by
  intro spec litLenCodes distCodes litBits distBits distExtraTailBits
    distExtraTailLen distTailBits distTailLen lenTailBits lenTailLen
    bitsTot lenTot bwLenStart bwDistStart bwDistExtraStart bwAll br0 brAfter
  rcases Png.lz77TokenExpand?_match_some_spec (out := out) (out' := out')
      (len := len) (distance := distance) hexpand with
    ⟨hlenLo, hlenHi, _hdistLo, _hdistHi, _hdistOut, _hdistSome, _hcopyFast⟩
  rcases Png.deflateLengthInfo_decodeLength_correct
      hlenInfo hlenLo hlenHi with
    ⟨_hsym, _hidxBase, _hidxExtra, _hextraLen, _hbaseLen, hbitsLenLt⟩
  rcases Png.deflateDistanceInfo_decodeDistance_correct hdistInfo with
    ⟨hdist, _hdistExtra, _hextraDist, _hbaseDist, hbitsDistLt⟩
  have hlitBitsLt : litBits < 2 ^ 9 := by
    have hbits :=
      generatedDynamicLitLenCodesLz77_match_bits_lt_codeSpace_at
        source target len distance htarget ht ⟨hlenLo, hlenHi⟩
    simpa [litBits, litLenCodes, hlenInfo] using hbits
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  have hdistSymLen : distSym < distLengths.size := by
    have hsize : distLengths.size = 30 := by
      simpa [distLengths] using
        generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
    have hbaseSize : Png.distBases.size = 30 := by decide
    omega
  have hdistBitsLt : distBits < 2 ^ 5 := by
    have hbits :=
      generatedDynamicDistCodesLz77_bits_lt_codeSpace
        (Png.distSymbolFreqsLz77 source) distSym hdistSymLen
    simpa [distBits, distCodes, distLengths] using hbits
  have hbwPrefix :
      Png.BitWriter.writeBits bw bitsTot 9 =
        Png.BitWriter.writeBits bw litBits 9 := by
    simpa [bitsTot] using
      Png.writeBits_or_shift_tail bw litBits lenTailBits 9 hlitBitsLt
  have hbwAllLenTail :
      bwAll =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw bitsTot 9) lenTailBits lenTailLen := by
    have hcat :=
      Png.writeBits_concat bw litBits lenTailBits 9 lenTailLen hlitBitsLt
    calc
      bwAll = Png.BitWriter.writeBits bw bitsTot (9 + lenTailLen) := by
          rfl
      _ =
          Png.BitWriter.writeBits (Png.BitWriter.writeBits bw litBits 9)
            lenTailBits lenTailLen := by
          simpa [bitsTot] using hcat
      _ =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bw bitsTot 9) lenTailBits lenTailLen := by
          rw [hbwPrefix]
  let brLen := Png.BitWriter.readerAt bwLenStart bwAll.flush
    (by
      have hk : 9 ≤ lenTot := by simp [lenTot]
      exact Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk)
    (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hbitLen : bwLenStart.bitPos < 8 := by
    simpa [bwLenStart] using
      Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit
  have hcurLen : bwLenStart.curClearAbove := by
    simpa [bwLenStart] using
      Png.curClearAbove_writeBits bw bitsTot 9 hbit hcur
  have hdecodeSym :
      spec.litLenTable.decode br0 = some (sym, brLen) := by
    have hdecode0 :=
      generatedDynamicLitLenTableLz77_decode_match_at_readerAt_writeBits
        source target len distance bw lenTailBits lenTailLen
        htarget ht ⟨hlenLo, hlenHi⟩ hbit hcur
    simpa [spec, generatedDynamicTableSpecLz77, litLenCodes, litBits,
      bitsTot, lenTot, bwAll, br0, brLen, hlenInfo] using hdecode0
  have hbwLenPrefix :
      Png.BitWriter.writeBits bwLenStart lenTailBits extraLen =
        Png.BitWriter.writeBits bwLenStart extraBits extraLen := by
    simpa [lenTailBits] using
      Png.writeBits_or_shift_tail bwLenStart extraBits distTailBits
        extraLen hbitsLenLt
  have hbwAllDistTail :
      bwAll =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bwLenStart lenTailBits extraLen)
          distTailBits distTailLen := by
    have hcat :=
      Png.writeBits_concat bwLenStart extraBits distTailBits
        extraLen distTailLen hbitsLenLt
    calc
      bwAll =
          Png.BitWriter.writeBits bwLenStart lenTailBits lenTailLen :=
            hbwAllLenTail
      _ =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwLenStart extraBits extraLen)
            distTailBits distTailLen := by
          simpa [lenTailBits, lenTailLen] using hcat
      _ =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwLenStart lenTailBits extraLen)
            distTailBits distTailLen := by
          rw [hbwLenPrefix]
  let brDist := Png.BitWriter.readerAt bwDistStart bwAll.flush
    (by
      simpa [bwDistStart, hbwAllDistTail] using
        Png.flush_size_writeBits_le
          (bw := bwDistStart) (bits := distTailBits) (len := distTailLen))
    (by
      simpa [bwDistStart] using
        Png.bitPos_lt_8_writeBits bwLenStart lenTailBits extraLen hbitLen)
  have hdecodeLenEx :
      ∃ hsym hbits,
        Png.decodeLength sym brLen hsym hbits = (len, brDist) := by
    have hdecode0 :=
      generatedDynamicPayloadLz77Match_decodeLength_readerAt_writeBits
        (bw := bwLenStart) (len := len) (sym := sym)
        (extraBits := extraBits) (extraLen := extraLen)
        (restBits := distTailBits) (restLen := distTailLen)
        hlenInfo ⟨hlenLo, hlenHi⟩ hbitLen hcurLen
    simpa [lenTailBits, lenTailLen, bwDistStart, brLen, brDist,
      hbwAllLenTail, hbwAllDistTail] using hdecode0
  have hbwDistPrefix :
      Png.BitWriter.writeBits bwDistStart distTailBits 5 =
        Png.BitWriter.writeBits bwDistStart distBits 5 := by
    simpa [distTailBits] using
      Png.writeBits_or_shift_tail bwDistStart distBits distExtraTailBits 5
        hdistBitsLt
  have hbwAllDistExtraTail :
      bwAll =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bwDistStart distTailBits 5)
          distExtraTailBits distExtraTailLen := by
    have hcat :=
      Png.writeBits_concat bwDistStart distBits distExtraTailBits
        5 distExtraTailLen hdistBitsLt
    calc
      bwAll =
          Png.BitWriter.writeBits bwDistStart distTailBits distTailLen :=
            hbwAllDistTail
      _ =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwDistStart distBits 5)
            distExtraTailBits distExtraTailLen := by
          simpa [distTailBits, distTailLen] using hcat
      _ =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwDistStart distTailBits 5)
            distExtraTailBits distExtraTailLen := by
          rw [hbwDistPrefix]
  let brCopy := Png.BitWriter.readerAt bwDistExtraStart bwAll.flush
    (by
      simpa [bwDistExtraStart, hbwAllDistExtraTail] using
        Png.flush_size_writeBits_le
          (bw := bwDistExtraStart) (bits := distExtraTailBits)
          (len := distExtraTailLen))
    (by
      have hbitDistSym' : bwDistStart.bitPos < 8 := by
        simpa [bwDistStart] using
          Png.bitPos_lt_8_writeBits bwLenStart lenTailBits extraLen hbitLen
      simpa [bwDistExtraStart] using
        Png.bitPos_lt_8_writeBits bwDistStart distTailBits 5 hbitDistSym')
  have hbitDistSym : bwDistStart.bitPos < 8 := by
    simpa [bwDistStart] using
      Png.bitPos_lt_8_writeBits bwLenStart lenTailBits extraLen hbitLen
  have hcurDistSym : bwDistStart.curClearAbove := by
    simpa [bwDistStart] using
      Png.curClearAbove_writeBits bwLenStart lenTailBits extraLen
        hbitLen hcurLen
  have hdecodeDistSym :
      spec.distTable.decode brDist = some (distSym, brCopy) := by
    have hdecode0 :=
      generatedDynamicDistTableLz77_decode_symbol_readerAt_writeBits
        (freqs := Png.distSymbolFreqsLz77 source) (sym := distSym)
        (bw := bwDistStart) (restBits := distExtraTailBits)
        (restLen := distExtraTailLen) hdistSymLen hbitDistSym hcurDistSym
    simpa [spec, generatedDynamicTableSpecLz77, distCodes, distLengths,
      distBits, distTailBits, distTailLen, bwDistExtraStart, brDist, brCopy,
      hbwAllDistTail, hbwAllDistExtraTail] using hdecode0
  have hbitDist : bwDistExtraStart.bitPos < 8 := by
    simpa [bwDistExtraStart] using
      Png.bitPos_lt_8_writeBits bwDistStart distTailBits 5 hbitDistSym
  have hcurDist : bwDistExtraStart.curClearAbove := by
    simpa [bwDistExtraStart] using
      Png.curClearAbove_writeBits bwDistStart distTailBits 5
        hbitDistSym hcurDistSym
  have hdecodeDistEx :
      ∃ hdist hbitsD,
        Png.decodeDistance distSym brCopy hdist hbitsD = (distance, brAfter) := by
    have hdecode0 :=
      generatedDynamicPayloadLz77Match_decodeDistance_readerAt_writeBits
        (bw := bwDistExtraStart) (distance := distance) (distSym := distSym)
        (distExtraBits := distExtraBits) (distExtraLen := distExtraLen)
        (restBits := tailBits) (restLen := tailLen) hdistInfo
        hbitDist hcurDist
    simpa [distExtraTailBits, distExtraTailLen, brCopy, brAfter,
      hbwAllDistExtraTail] using hdecode0
  have hcopy : Png.copyDistance out distance len = some out' :=
    Png.lz77TokenExpand?_match_some_copyDistance hexpand
  exact dynamicPayloadTransition_lz77_copy_of_decodes
    (spec := spec) (br0 := br0) (br1 := brLen) (br2 := brDist)
    (br3 := brCopy) (br4 := brAfter) (out := out) (out' := out')
    (len := len) (distance := distance) (sym := sym)
    (extraBits := extraBits) (extraLen := extraLen) (distSym := distSym)
    (distExtraBits := distExtraBits) (distExtraLen := distExtraLen)
    hlenInfo hdistInfo ⟨hlenLo, hlenHi⟩
    hdecodeSym hdecodeLenEx hdecodeDistSym hdecodeDistEx hcopy

set_option maxRecDepth 250000 in
set_option maxHeartbeats 6000000 in
/-- Runtime-shaped generated dynamic LZ77 match-token bits produce one
generic dynamic-payload copy transition. This bridges the packed token stream
to the split length/distance replay lemma. -/
lemma generatedDynamicPayloadLz77Match_transition_readerAt_writeBits
    (source : Array Png.Lz77Token) (target : Nat)
    (bw : Png.BitWriter) (out out' : ByteArray)
    (len distance sym extraBits extraLen distSym distExtraBits distExtraLen : Nat)
    (tailBits tailLen : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.Lz77Token.match len distance)
    (hlenInfo : Png.deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo :
      Png.deflateDistanceInfo? distance =
        some (distSym, distExtraBits, distExtraLen))
    (hexpand : Png.lz77TokenExpand? out (.match len distance) = some out')
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpecLz77 source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    let bits :=
      dynamicPayloadLz77TokenBits litLenCodes distCodes
        (Png.Lz77Token.match len distance)
    let tokenLen :=
      dynamicPayloadLz77TokenBitLen litLenCodes distCodes
        (Png.Lz77Token.match len distance)
    let bitsTot := bits ||| (tailBits <<< tokenLen)
    let lenTot := tokenLen + tailLen
    let bwAll := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot tokenLen) bwAll.flush
      (by
        have hk : tokenLen ≤ lenTot := by omega
        simpa [lenTot] using
          Png.flush_size_writeBits_prefix bw bitsTot tokenLen lenTot hk)
      (Png.bitPos_lt_8_writeBits bw bitsTot tokenLen hbit)
    Png.DynamicPayloadTransition spec br0 out brAfter out' := by
  intro spec litLenCodes distCodes bits tokenLen bitsTot lenTot bwAll br0
    brAfter
  rcases Png.lz77TokenExpand?_match_some_spec (out := out) (out' := out')
      (len := len) (distance := distance) hexpand with
    ⟨hlenLo, hlenHi, _hdistLo, _hdistHi, _hdistOut, _hdistSome, _hcopyFast⟩
  rcases Png.deflateLengthInfo_decodeLength_correct
      hlenInfo hlenLo hlenHi with
    ⟨_hsym, _hidxBase, _hidxExtra, _hextraLen, _hbaseLen, hbitsLenLt⟩
  rcases Png.deflateDistanceInfo_decodeDistance_correct hdistInfo with
    ⟨hdist, _hdistExtra, _hextraDist, _hbaseDist, hbitsDistLt⟩
  let litBits := litLenCodes[sym]!.1
  let distBits := distCodes[distSym]!.1
  let distExtraTailBits := distExtraBits ||| (tailBits <<< distExtraLen)
  let distExtraTailLen := distExtraLen + tailLen
  let distTailBits := distBits ||| (distExtraTailBits <<< 5)
  let distTailLen := 5 + distExtraTailLen
  let lenTailBits := extraBits ||| (distTailBits <<< extraLen)
  let lenTailLen := extraLen + distTailLen
  let manualBitsTot := litBits ||| (lenTailBits <<< 9)
  let manualLenTot := 9 + lenTailLen
  let bwManualAll := Png.BitWriter.writeBits bw manualBitsTot manualLenTot
  let bwLenStart := Png.BitWriter.writeBits bw manualBitsTot 9
  let bwDistStart := Png.BitWriter.writeBits bwLenStart lenTailBits extraLen
  let bwDistExtraStart := Png.BitWriter.writeBits bwDistStart distTailBits 5
  let manualAllAfter :=
    Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits distExtraTailLen
  let brAfterSeq := Png.BitWriter.readerAt
    (Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits distExtraLen)
    manualAllAfter.flush
    (by
      have hk : distExtraLen ≤ distExtraTailLen := by
        simp [distExtraTailLen]
      exact Png.flush_size_writeBits_prefix bwDistExtraStart
        distExtraTailBits distExtraLen distExtraTailLen hk)
    (Png.bitPos_lt_8_writeBits bwDistExtraStart distExtraTailBits
      distExtraLen
      (Png.bitPos_lt_8_writeBits bwDistStart distTailBits 5
        (Png.bitPos_lt_8_writeBits bwLenStart lenTailBits extraLen
          (Png.bitPos_lt_8_writeBits bw manualBitsTot 9 hbit))))
  have hbitsShape : bitsTot = manualBitsTot := by
    have h :=
      dynamicPayloadLz77TokenBits_generated_match_tail_eq
        source target len distance htarget ht ⟨hlenLo, hlenHi⟩
        hlenInfo hdistInfo tailBits
    simpa [bitsTot, bits, tokenLen, litLenCodes, distCodes, litBits,
      distBits, distExtraTailBits, distTailBits, lenTailBits,
      manualBitsTot] using h
  have hlenShape : lenTot = manualLenTot := by
    have h :=
      dynamicPayloadLz77TokenBitLen_generated_match_tail_eq
        source target len distance htarget ht ⟨hlenLo, hlenHi⟩
        hlenInfo hdistInfo tailLen
    simpa [lenTot, tokenLen, litLenCodes, distCodes, distExtraTailLen,
      distTailLen, lenTailLen, manualLenTot, Nat.add_assoc] using h
  have htokenLen :
      tokenLen = 9 + extraLen + 5 + distExtraLen := by
    have h :=
      dynamicPayloadLz77TokenBitLen_generated_match_eq
        source target len distance htarget ht ⟨hlenLo, hlenHi⟩
        hlenInfo hdistInfo
    simpa [tokenLen, litLenCodes, distCodes, Nat.add_assoc] using h
  have hlitBitsLt : litBits < 2 ^ 9 := by
    have hbits :=
      generatedDynamicLitLenCodesLz77_match_bits_lt_codeSpace_at
        source target len distance htarget ht ⟨hlenLo, hlenHi⟩
    simpa [litBits, litLenCodes, hlenInfo] using hbits
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  have hdistSymLen : distSym < distLengths.size := by
    have hsize : distLengths.size = 30 := by
      simpa [distLengths] using
        generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
    have hbaseSize : Png.distBases.size = 30 := by decide
    omega
  have hdistBitsLt : distBits < 2 ^ 5 := by
    have hbits :=
      generatedDynamicDistCodesLz77_bits_lt_codeSpace
        (Png.distSymbolFreqsLz77 source) distSym hdistSymLen
    simpa [distBits, distCodes, distLengths] using hbits
  have hbwLenStartPrefix :
      bwLenStart = Png.BitWriter.writeBits bw litBits 9 := by
    simpa [bwLenStart, manualBitsTot] using
      Png.writeBits_or_shift_tail bw litBits lenTailBits 9 hlitBitsLt
  have hbwManualAllLenTail :
      bwManualAll =
        Png.BitWriter.writeBits bwLenStart lenTailBits lenTailLen := by
    have hcat :=
      Png.writeBits_concat bw litBits lenTailBits 9 lenTailLen hlitBitsLt
    simpa [bwManualAll, manualBitsTot, manualLenTot, bwLenStart,
      hbwLenStartPrefix] using hcat
  have hbwDistStartPrefix :
      bwDistStart =
        Png.BitWriter.writeBits bwLenStart extraBits extraLen := by
    simpa [bwDistStart, lenTailBits] using
      Png.writeBits_or_shift_tail bwLenStart extraBits distTailBits
        extraLen hbitsLenLt
  have hbwManualAllDistTail :
      bwManualAll =
        Png.BitWriter.writeBits bwDistStart distTailBits distTailLen := by
    have hcat :=
      Png.writeBits_concat bwLenStart extraBits distTailBits
        extraLen distTailLen hbitsLenLt
    calc
      bwManualAll =
          Png.BitWriter.writeBits bwLenStart lenTailBits lenTailLen :=
            hbwManualAllLenTail
      _ =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwLenStart extraBits extraLen)
            distTailBits distTailLen := by
          simpa [lenTailBits, lenTailLen] using hcat
      _ = Png.BitWriter.writeBits bwDistStart distTailBits distTailLen := by
          rw [hbwDistStartPrefix]
  have hbwDistExtraStartPrefix :
      bwDistExtraStart =
        Png.BitWriter.writeBits bwDistStart distBits 5 := by
    simpa [bwDistExtraStart, distTailBits] using
      Png.writeBits_or_shift_tail bwDistStart distBits distExtraTailBits 5
        hdistBitsLt
  have hbwManualAllDistExtraTail :
      bwManualAll = manualAllAfter := by
    have hcat :=
      Png.writeBits_concat bwDistStart distBits distExtraTailBits
        5 distExtraTailLen hdistBitsLt
    calc
      bwManualAll =
          Png.BitWriter.writeBits bwDistStart distTailBits distTailLen :=
            hbwManualAllDistTail
      _ =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwDistStart distBits 5)
            distExtraTailBits distExtraTailLen := by
          simpa [distTailBits, distTailLen] using hcat
      _ = manualAllAfter := by
          simp [manualAllAfter, hbwDistExtraStartPrefix]
  have hwriterLit :
      Png.BitWriter.writeBits bw manualBitsTot
          (9 + (extraLen + (5 + distExtraLen))) =
        Png.BitWriter.writeBits bwLenStart lenTailBits
          (extraLen + (5 + distExtraLen)) := by
    have hcat :=
      Png.writeBits_concat bw litBits lenTailBits 9
        (extraLen + (5 + distExtraLen)) hlitBitsLt
    simpa [manualBitsTot, bwLenStart, hbwLenStartPrefix,
      Nat.add_assoc] using hcat
  have hwriterLen :
      Png.BitWriter.writeBits bwLenStart lenTailBits
          (extraLen + (5 + distExtraLen)) =
        Png.BitWriter.writeBits bwDistStart distTailBits
          (5 + distExtraLen) := by
    have hcat :=
      Png.writeBits_concat bwLenStart extraBits distTailBits
        extraLen (5 + distExtraLen) hbitsLenLt
    calc
      Png.BitWriter.writeBits bwLenStart lenTailBits
          (extraLen + (5 + distExtraLen)) =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwLenStart extraBits extraLen)
            distTailBits (5 + distExtraLen) := by
          simpa [lenTailBits] using hcat
      _ = Png.BitWriter.writeBits bwDistStart distTailBits
          (5 + distExtraLen) := by
          rw [hbwDistStartPrefix]
  have hwriterDist :
      Png.BitWriter.writeBits bwDistStart distTailBits (5 + distExtraLen) =
        Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits
          distExtraLen := by
    have hcat :=
      Png.writeBits_concat bwDistStart distBits distExtraTailBits
        5 distExtraLen hdistBitsLt
    calc
      Png.BitWriter.writeBits bwDistStart distTailBits (5 + distExtraLen) =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwDistStart distBits 5)
            distExtraTailBits distExtraLen := by
          simpa [distTailBits] using hcat
      _ =
          Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits
            distExtraLen := by
          rw [hbwDistExtraStartPrefix]
  have hwriterPrefix :
      Png.BitWriter.writeBits bw bitsTot tokenLen =
        Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits
          distExtraLen := by
    calc
      Png.BitWriter.writeBits bw bitsTot tokenLen =
          Png.BitWriter.writeBits bw manualBitsTot
            (9 + (extraLen + (5 + distExtraLen))) := by
          simp [hbitsShape, htokenLen, Nat.add_assoc]
      _ =
          Png.BitWriter.writeBits bwLenStart lenTailBits
            (extraLen + (5 + distExtraLen)) := hwriterLit
      _ =
          Png.BitWriter.writeBits bwDistStart distTailBits
            (5 + distExtraLen) := hwriterLen
      _ =
          Png.BitWriter.writeBits bwDistExtraStart distExtraTailBits
            distExtraLen := hwriterDist
  have hfullPublicManual : bwAll = manualAllAfter := by
    calc
      bwAll = bwManualAll := by
          simp [bwAll, bitsTot, lenTot, hbitsShape, hlenShape,
            bwManualAll, manualBitsTot, manualLenTot]
      _ = manualAllAfter := hbwManualAllDistExtraTail
  have hbrAfterEq : brAfterSeq = brAfter := by
    refine readerAt_eq_of_eqs hwriterPrefix.symm ?_ _ _ _ _
    exact (congrArg Png.BitWriter.flush hfullPublicManual).symm
  have hmanual :=
    generatedDynamicPayloadLz77Match_manual_transition_readerAt_writeBits
      (source := source) (target := target) (bw := bw) (out := out)
      (out' := out') (len := len) (distance := distance) (sym := sym)
      (extraBits := extraBits) (extraLen := extraLen) (distSym := distSym)
      (distExtraBits := distExtraBits) (distExtraLen := distExtraLen)
      (tailBits := tailBits) (tailLen := tailLen)
      htarget ht hlenInfo hdistInfo hexpand hbit hcur
  have hmanualSeq :
      Png.DynamicPayloadTransition spec br0 out brAfterSeq out' := by
    simpa [spec, litLenCodes, distCodes, litBits, distBits,
      distExtraTailBits, distExtraTailLen, distTailBits, distTailLen,
      lenTailBits, lenTailLen, manualBitsTot, manualLenTot, bwManualAll,
      bwLenStart, bwDistStart, bwDistExtraStart, manualAllAfter,
      brAfterSeq, bits, tokenLen, bitsTot, lenTot, bwAll, br0,
      hbitsShape, hlenShape] using hmanual
  simpa [hbrAfterEq] using hmanualSeq

/-- Proof-facing expansion of an LZ77 token list. It mirrors the array
expander while giving payload trace proofs structural recursion on lists. -/
def lz77TokensExpandList? (out : ByteArray) :
    List Png.Lz77Token → Option ByteArray
  | [] => some out
  | token :: tokens =>
      match Png.lz77TokenExpand? out token with
      | some out' => lz77TokensExpandList? out' tokens
      | none => none

/-- Expanding the suffix of an array-backed LZ77 token stream is the same as
expanding the corresponding dropped `toList` suffix. This connects runtime
array recursion to the proof-facing list trace. -/
lemma lz77TokensExpandList?_drop_eq_deflateTokensExpandLz77From?
    (tokens : Array Png.Lz77Token) :
    ∀ i out,
      lz77TokensExpandList? out (tokens.toList.drop i) =
        Png.deflateTokensExpandLz77From? tokens i out := by
  classical
  have hk :
      ∀ k, ∀ i out,
        tokens.size - i = k →
        lz77TokensExpandList? out (tokens.toList.drop i) =
          Png.deflateTokensExpandLz77From? tokens i out := by
    intro k
    induction k with
    | zero =>
        intro i out hk
        have hnot : ¬ i < tokens.size := by omega
        have hle : tokens.toList.length ≤ i := by
          simpa using Nat.le_of_not_gt hnot
        have hdrop : tokens.toList.drop i = [] :=
          List.drop_eq_nil_of_le hle
        rw [Png.deflateTokensExpandLz77From?]
        simp [hnot, hdrop, lz77TokensExpandList?]
    | succ k ih =>
        intro i out hk
        have hi : i < tokens.size := by omega
        have hlist : i < tokens.toList.length := by
          simpa using hi
        have hget : tokens.toList[i]'hlist = tokens[i]'hi := by
          simp
        have hdrop :
            tokens.toList.drop i =
              tokens[i]'hi :: tokens.toList.drop (i + 1) := by
          calc
            tokens.toList.drop i =
                tokens.toList[i]'hlist :: tokens.toList.drop (i + 1) :=
                  List.drop_eq_getElem_cons hlist
            _ = tokens[i]'hi :: tokens.toList.drop (i + 1) := by
                  rw [hget]
        rw [Png.deflateTokensExpandLz77From?]
        simp [hi, hdrop, lz77TokensExpandList?]
        cases hstep : Png.lz77TokenExpand? out (tokens[i]'hi) with
        | none =>
            simp [hstep]
        | some outNext =>
            simp [hstep]
            have hkTail : tokens.size - (i + 1) = k := by omega
            exact ih (i + 1) outNext hkTail
  intro i out
  exact hk (tokens.size - i) i out rfl

/-- The public greedy LZ77 token stream expands through the proof-facing list
expander to the original raw bytes. -/
lemma lz77TokensExpandList_deflateTokensLz77 (raw : ByteArray) :
    lz77TokensExpandList? ByteArray.empty
        (Png.deflateTokensLz77 raw).toList = some raw := by
  have hlist :=
    lz77TokensExpandList?_drop_eq_deflateTokensExpandLz77From?
      (Png.deflateTokensLz77 raw) 0 ByteArray.empty
  have hexpand :=
    deflateTokensExpandLz77_deflateTokensLz77 raw
  calc
    lz77TokensExpandList? ByteArray.empty
        (Png.deflateTokensLz77 raw).toList =
        Png.deflateTokensExpandLz77From? (Png.deflateTokensLz77 raw)
          0 ByteArray.empty := by
          simpa using hlist
    _ = some raw := by
          simpa [Png.deflateTokensExpandLz77?] using hexpand

set_option maxRecDepth 250000 in
set_option maxHeartbeats 6000000 in
/-- Replays a generated dynamic LZ77 payload-token list through the generic
dynamic-Huffman payload trace. This is the recursive bridge from emitted
LZ77 token bits to decoded output bytes. -/
lemma generatedDynamicPayloadLz77TraceList_readerAt_writeBits
    (source : Array Png.Lz77Token) (tokens : List Png.Lz77Token)
    (hmember :
      ∀ token ∈ tokens, ∃ target, ∃ htarget : target < source.size,
        source[target]'htarget = token)
    (out outFinal : ByteArray)
    (hexpand : lz77TokensExpandList? out tokens = some outFinal)
    (bw : Png.BitWriter)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpecLz77 source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    let bits := dynamicPayloadLz77StreamBits litLenCodes distCodes tokens
    let len := dynamicPayloadLz77StreamLen litLenCodes distCodes tokens
    let bwAll := Png.BitWriter.writeBits bw bits len
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bits len) hbit
    let brAfter := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bits len)
      bwAll.flush
      (by
        simpa [bwAll] using
          (le_rfl : (Png.BitWriter.writeBits bw bits len).flush.size ≤
            (Png.BitWriter.writeBits bw bits len).flush.size))
      (Png.bitPos_lt_8_writeBits bw bits len hbit)
    Png.DynamicPayloadTrace spec (tokens.length + 1) br0 out brAfter
      outFinal := by
  revert hmember out outFinal bw
  induction tokens with
  | nil =>
      intro _hmember out outFinal hexpand bw hbit hcur spec litLenCodes
        distCodes bits len bwAll br0 brAfter
      simp [lz77TokensExpandList?] at hexpand
      subst outFinal
      have htrace :=
        generatedDynamicPayloadLz77Eob_finish_readerAt_writeBits
          (source := source) (bw := bw) (out := out) hbit hcur
      exact Png.DynamicPayloadTrace.finish (by
        simpa [spec, litLenCodes, distCodes, bits, len, bwAll, br0,
          brAfter, dynamicPayloadLz77StreamBits,
          dynamicPayloadLz77StreamLen] using htrace)
  | cons token tokens ih =>
      intro hmember out outFinal hexpand bw hbit hcur spec litLenCodes
        distCodes bits len bwAll br0 brAfter
      have htailMember :
          ∀ t ∈ tokens, ∃ target, ∃ htarget : target < source.size,
            source[target]'htarget = t := by
        intro t ht
        exact hmember t (List.mem_cons_of_mem token ht)
      let tokenBits := dynamicPayloadLz77TokenBits litLenCodes distCodes token
      let tokenLen := dynamicPayloadLz77TokenBitLen litLenCodes distCodes token
      let tailBits := dynamicPayloadLz77StreamBits litLenCodes distCodes tokens
      let tailLen := dynamicPayloadLz77StreamLen litLenCodes distCodes tokens
      let bwMid := Png.BitWriter.writeBits bw bits tokenLen
      let brMid := Png.BitWriter.readerAt bwMid bwAll.flush
        (by
          have hk : tokenLen ≤ len := by
            simp [len, dynamicPayloadLz77StreamLen, tokenLen, tailLen]
          simpa [bwMid, bwAll] using
            Png.flush_size_writeBits_prefix bw bits tokenLen len hk)
        (Png.bitPos_lt_8_writeBits bw bits tokenLen hbit)
      let bwTailAll :=
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw tokenBits tokenLen) tailBits tailLen
      have hbitMid :
          (Png.BitWriter.writeBits bw tokenBits tokenLen).bitPos < 8 :=
        Png.bitPos_lt_8_writeBits bw tokenBits tokenLen hbit
      have hcurMid :
          (Png.BitWriter.writeBits bw tokenBits tokenLen).curClearAbove :=
        Png.curClearAbove_writeBits bw tokenBits tokenLen hbit hcur
      cases token with
      | literal b =>
          simp [lz77TokensExpandList?, Png.lz77TokenExpand?] at hexpand
          rcases hmember (Png.Lz77Token.literal b) (by simp) with
            ⟨target, htarget, ht⟩
          have htokenBits :
              tokenBits < 2 ^ tokenLen := by
            simpa [litLenCodes, distCodes, tokenBits, tokenLen] using
              dynamicPayloadLz77TokenBits_generated_literal_lt_codeSpace_at
                source target b htarget ht
          have hprefix :
              bwMid = Png.BitWriter.writeBits bw tokenBits tokenLen := by
            simpa [bwMid, bits, dynamicPayloadLz77StreamBits, tokenBits,
              tokenLen, tailBits] using
              Png.writeBits_or_shift_tail bw tokenBits tailBits tokenLen
                htokenBits
          have hconcat :
              bwAll = bwTailAll := by
            have h :=
              Png.writeBits_concat bw tokenBits tailBits tokenLen tailLen
                htokenBits
            simpa [bwAll, bits, len, dynamicPayloadLz77StreamBits,
              dynamicPayloadLz77StreamLen, tokenBits, tokenLen, tailBits,
              tailLen, bwTailAll] using h
          have hbrMidEq :
              brMid =
                Png.BitWriter.readerAt
                  (Png.BitWriter.writeBits bw tokenBits tokenLen)
                  bwTailAll.flush
                  (Png.flush_size_writeBits_le
                    (Png.BitWriter.writeBits bw tokenBits tokenLen)
                    tailBits tailLen)
                  hbitMid := by
            refine readerAt_eq_of_eqs hprefix ?_ _ _ _ _
            simpa [hconcat]
          have hstep :=
            generatedDynamicPayloadLz77Literal_transition_readerAt_writeBits
              (source := source) (target := target) (b := b) (bw := bw)
              (out := out) (tailBits := tailBits) (tailLen := tailLen)
              htarget ht hbit hcur
          have hstep' :
              Png.DynamicPayloadTransition spec br0 out brMid
                (out.push b) := by
            simpa [spec, litLenCodes, distCodes, tokenBits, tokenLen,
              tailBits, tailLen, bits, len, bwAll, br0, brMid,
              dynamicPayloadLz77StreamBits, dynamicPayloadLz77StreamLen]
              using hstep
          have hrestRaw :=
            ih htailMember (out.push b) outFinal hexpand
              (Png.BitWriter.writeBits bw tokenBits tokenLen)
              hbitMid hcurMid
          have hrest :
              Png.DynamicPayloadTrace spec (tokens.length + 1) brMid
                (out.push b) brAfter outFinal := by
            have hbrAfterEq :
                Png.BitWriter.readerAt
                    (Png.BitWriter.writeBits
                      (Png.BitWriter.writeBits bw tokenBits tokenLen)
                      tailBits tailLen)
                    bwTailAll.flush
                    (by
                      simpa [bwTailAll] using
                        (le_rfl :
                          (Png.BitWriter.writeBits
                            (Png.BitWriter.writeBits bw tokenBits tokenLen)
                            tailBits tailLen).flush.size ≤
                          (Png.BitWriter.writeBits
                            (Png.BitWriter.writeBits bw tokenBits tokenLen)
                            tailBits tailLen).flush.size))
                    (Png.bitPos_lt_8_writeBits
                      (Png.BitWriter.writeBits bw tokenBits tokenLen)
                      tailBits tailLen hbitMid) = brAfter := by
              refine readerAt_eq_of_eqs ?_ ?_ _ _ _ _
              · simpa [bwAll, bwTailAll] using hconcat.symm
              · simpa [bwAll, bwTailAll] using
                  congrArg Png.BitWriter.flush hconcat.symm
            have hrest' := hrestRaw
            simpa [spec, litLenCodes, distCodes, tailBits, tailLen,
              bwTailAll, hbrMidEq, hbrAfterEq] using hrest'
          exact Png.DynamicPayloadTrace.step (hstep := hstep') (hrest := hrest)
      | «match» matchLen distance =>
          cases hstepToken :
              Png.lz77TokenExpand? out (Png.Lz77Token.match matchLen distance) with
          | none =>
              simp [lz77TokensExpandList?, hstepToken] at hexpand
          | some outNext =>
              simp [lz77TokensExpandList?, hstepToken] at hexpand
              rcases hmember (Png.Lz77Token.match matchLen distance) (by simp) with
                ⟨target, htarget, ht⟩
              rcases Png.lz77TokenExpand?_match_some_spec
                  (out := out) (out' := outNext)
                  (len := matchLen) (distance := distance) hstepToken with
                ⟨hlenLo, hlenHi, _hdistLo, _hdistHi, _hdistOut,
                  hinfoSome, _hcopyFast⟩
              rcases hlenInfo : Png.deflateLengthInfo matchLen with
                ⟨sym, extraBits, extraLen⟩
              cases hdistInfo : Png.deflateDistanceInfo? distance with
              | none =>
                  rcases hinfoSome with ⟨info, hinfo⟩
                  simp [hdistInfo] at hinfo
              | some distInfo =>
                  rcases distInfo with ⟨distSym, distExtraBits, distExtraLen⟩
                  have htokenBits :
                      tokenBits < 2 ^ tokenLen := by
                    simpa [litLenCodes, distCodes, tokenBits, tokenLen] using
                      dynamicPayloadLz77TokenBits_generated_match_lt_codeSpace_at
                        source target matchLen distance htarget ht
                        ⟨hlenLo, hlenHi⟩ hdistInfo
                  have hprefix :
                      bwMid = Png.BitWriter.writeBits bw tokenBits tokenLen := by
                    simpa [bwMid, bits, dynamicPayloadLz77StreamBits, tokenBits,
                      tokenLen, tailBits] using
                      Png.writeBits_or_shift_tail bw tokenBits tailBits tokenLen
                        htokenBits
                  have hconcat :
                      bwAll = bwTailAll := by
                    have h :=
                      Png.writeBits_concat bw tokenBits tailBits tokenLen tailLen
                        htokenBits
                    simpa [bwAll, bits, len, dynamicPayloadLz77StreamBits,
                      dynamicPayloadLz77StreamLen, tokenBits, tokenLen, tailBits,
                      tailLen, bwTailAll] using h
                  have hbrMidEq :
                      brMid =
                        Png.BitWriter.readerAt
                          (Png.BitWriter.writeBits bw tokenBits tokenLen)
                          bwTailAll.flush
                          (Png.flush_size_writeBits_le
                            (Png.BitWriter.writeBits bw tokenBits tokenLen)
                            tailBits tailLen)
                          hbitMid := by
                    refine readerAt_eq_of_eqs hprefix ?_ _ _ _ _
                    simpa [hconcat]
                  have hstep :=
                    generatedDynamicPayloadLz77Match_transition_readerAt_writeBits
                      (source := source) (target := target) (bw := bw)
                      (out := out) (out' := outNext) (len := matchLen)
                      (distance := distance) (sym := sym)
                      (extraBits := extraBits) (extraLen := extraLen)
                      (distSym := distSym) (distExtraBits := distExtraBits)
                      (distExtraLen := distExtraLen)
                      (tailBits := tailBits) (tailLen := tailLen)
                      htarget ht hlenInfo hdistInfo hstepToken hbit hcur
                  have hstep' :
                      Png.DynamicPayloadTransition spec br0 out brMid
                        outNext := by
                    simpa [spec, litLenCodes, distCodes, tokenBits, tokenLen,
                      tailBits, tailLen, bits, len, bwAll, br0, brMid,
                      dynamicPayloadLz77StreamBits,
                      dynamicPayloadLz77StreamLen] using hstep
                  have hrestRaw :=
                    ih htailMember outNext outFinal hexpand
                      (Png.BitWriter.writeBits bw tokenBits tokenLen)
                      hbitMid hcurMid
                  have hrest :
                      Png.DynamicPayloadTrace spec (tokens.length + 1) brMid
                        outNext brAfter outFinal := by
                    have hbrAfterEq :
                        Png.BitWriter.readerAt
                            (Png.BitWriter.writeBits
                              (Png.BitWriter.writeBits bw tokenBits tokenLen)
                              tailBits tailLen)
                            bwTailAll.flush
                            (by
                              simpa [bwTailAll] using
                                (le_rfl :
                                  (Png.BitWriter.writeBits
                                    (Png.BitWriter.writeBits bw tokenBits tokenLen)
                                    tailBits tailLen).flush.size ≤
                                  (Png.BitWriter.writeBits
                                    (Png.BitWriter.writeBits bw tokenBits tokenLen)
                                    tailBits tailLen).flush.size))
                            (Png.bitPos_lt_8_writeBits
                              (Png.BitWriter.writeBits bw tokenBits tokenLen)
                              tailBits tailLen hbitMid) = brAfter := by
                      refine readerAt_eq_of_eqs ?_ ?_ _ _ _ _
                      · simpa [bwAll, bwTailAll] using hconcat.symm
                      · simpa [bwAll, bwTailAll] using
                          congrArg Png.BitWriter.flush hconcat.symm
                    have hrest' := hrestRaw
                    simpa [spec, litLenCodes, distCodes, tailBits, tailLen,
                      bwTailAll, hbrMidEq, hbrAfterEq] using hrest'
                  exact Png.DynamicPayloadTrace.step
                    (hstep := hstep') (hrest := hrest)

/-- Generated dynamic LZ77 payload streams have at least one bit per replay
step. This supplies the decoder-fuel bound for LZ77 token traces. -/
lemma dynamicPayloadLz77StreamLen_generated_ge_steps
    (source : Array Png.Lz77Token) (tokens : List Png.Lz77Token)
    (hvalid :
      ∀ target (htarget : target < source.size),
        Png.Lz77TokenFixedValid (source[target]'htarget))
    (hmember :
      ∀ token ∈ tokens, ∃ target, ∃ htarget : target < source.size,
        source[target]'htarget = token) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    tokens.length + 1 ≤
      dynamicPayloadLz77StreamLen litLenCodes distCodes tokens := by
  induction tokens with
  | nil =>
      intro litLenCodes distCodes
      have hlen : dynamicPayloadLz77EobBitLen litLenCodes = 9 := by
        simpa [litLenCodes] using
          dynamicPayloadLz77EobBitLen_generated_eq_nine source
      change 1 ≤ dynamicPayloadLz77EobBitLen litLenCodes
      rw [hlen]
      decide
  | cons token tokens ih =>
      intro litLenCodes distCodes
      have htailMember :
          ∀ t ∈ tokens, ∃ target, ∃ htarget : target < source.size,
            source[target]'htarget = t := by
        intro t ht
        exact hmember t (List.mem_cons_of_mem token ht)
      have htail := ih htailMember
      have htail' :
          tokens.length + 1 ≤
            dynamicPayloadLz77StreamLen litLenCodes distCodes tokens := by
        simpa [litLenCodes, distCodes] using htail
      have htokenLenPos :
          1 ≤ dynamicPayloadLz77TokenBitLen litLenCodes distCodes token := by
        cases token with
        | literal b =>
            rcases hmember (Png.Lz77Token.literal b) (by simp) with
              ⟨target, htarget, ht⟩
            have hlen :
                dynamicPayloadLz77TokenBitLen litLenCodes distCodes
                  (Png.Lz77Token.literal b) = 9 := by
              simpa [litLenCodes, distCodes] using
                dynamicPayloadLz77TokenBitLen_generated_literal_eq_nine_at
                  source target b htarget ht
            omega
        | «match» len distance =>
            rcases hmember (Png.Lz77Token.match len distance) (by simp) with
              ⟨target, htarget, ht⟩
            have hv := hvalid target htarget
            simp [Png.Lz77TokenFixedValid, ht] at hv
            rcases hv with ⟨hlenLo, hlenHi, hdistSome⟩
            rcases hlenInfo : Png.deflateLengthInfo len with
              ⟨sym, extraBits, extraLen⟩
            cases hdistInfo : Png.deflateDistanceInfo? distance with
            | none =>
                rcases hdistSome with ⟨info, hinfo⟩
                simp [hdistInfo] at hinfo
            | some distInfo =>
                rcases distInfo with ⟨distSym, distExtraBits, distExtraLen⟩
                have hlen :
                    dynamicPayloadLz77TokenBitLen litLenCodes distCodes
                      (Png.Lz77Token.match len distance) =
                        9 + extraLen + 5 + distExtraLen := by
                  simpa [litLenCodes, distCodes, Nat.add_assoc] using
                    dynamicPayloadLz77TokenBitLen_generated_match_eq
                      source target len distance htarget ht
                      ⟨hlenLo, hlenHi⟩ hlenInfo hdistInfo
                omega
      simp [dynamicPayloadLz77StreamLen]
      omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Generated dynamic LZ77 payload bits are accepted by the generic
compressed-block decoder and produce the list expansion output. -/
lemma decodeCompressedBlock_generatedDynamicPayloadLz77_readerAt_writeBits
    (source : Array Png.Lz77Token) (raw : ByteArray)
    (hvalid :
      ∀ target (htarget : target < source.size),
        Png.Lz77TokenFixedValid (source[target]'htarget))
    (hexpand :
      lz77TokensExpandList? ByteArray.empty source.toList = some raw)
    (bw : Png.BitWriter)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpecLz77 source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    let bits := dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let len := dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let bwAll := Png.BitWriter.writeBits bw bits len
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bits len) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bits len) bwAll.flush
      (by
        simpa [bwAll] using
          (le_rfl : (Png.BitWriter.writeBits bw bits len).flush.size ≤
            (Png.BitWriter.writeBits bw bits len).flush.size))
      (Png.bitPos_lt_8_writeBits bw bits len hbit)
    Png.decodeCompressedBlock spec.litLenTable spec.distTable br0
      ByteArray.empty = some (brAfter, raw) := by
  intro spec litLenCodes distCodes bits len bwAll br0 brAfter
  have htrace :=
    generatedDynamicPayloadLz77TraceList_readerAt_writeBits
      (source := source) (tokens := source.toList)
      (fun token hmem => lz77Token_mem_toList_index hmem)
      (out := ByteArray.empty) (outFinal := raw) hexpand
      (bw := bw) hbit hcur
  have htrace' :
      Png.DynamicPayloadTrace spec (source.toList.length + 1) br0
        ByteArray.empty brAfter raw := by
    simpa [spec, litLenCodes, distCodes, bits, len, bwAll, br0, brAfter]
      using htrace
  have hstepsLen :
      source.toList.length + 1 ≤ len := by
    have h :=
      dynamicPayloadLz77StreamLen_generated_ge_steps
        (source := source) (tokens := source.toList) hvalid
        (fun token hmem => lz77Token_mem_toList_index hmem)
    simpa [litLenCodes, distCodes, len] using h
  have hlenLeData : len ≤ br0.data.size * 8 := by
    have hlenLeBitCount : len ≤ bwAll.bitCount := by
      have h := Nat.le_add_left len bw.bitCount
      simpa [bwAll, Png.bitCount_writeBits, Nat.add_comm] using h
    have hbitCountLe : bwAll.bitCount ≤ bwAll.flush.size * 8 :=
      Png.flush_size_mul_ge_bitCount (bw := bwAll) (hbit := bwAll.hbit)
    exact le_trans hlenLeBitCount
      (by simpa [br0, Png.BitWriter.readerAt] using hbitCountLe)
  have hfuel : source.toList.length + 1 ≤ br0.data.size * 8 + 1 := by
    omega
  exact Png.decodeCompressedBlock_of_trace htrace' hfuel

/-- Payload decoder specialization for the public generated LZ77 tokenizer:
decoding the generated dynamic payload reconstructs the original raw bytes. -/
lemma decodeCompressedBlock_deflateTokensLz77Payload_readerAt_writeBits
    (raw : ByteArray) (bw : Png.BitWriter)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let source := Png.deflateTokensLz77 raw
    let spec := generatedDynamicTableSpecLz77 source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source))
    let bits := dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let len := dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let bwAll := Png.BitWriter.writeBits bw bits len
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bits len) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bits len) bwAll.flush
      (by
        simpa [bwAll] using
          (le_rfl : (Png.BitWriter.writeBits bw bits len).flush.size ≤
            (Png.BitWriter.writeBits bw bits len).flush.size))
      (Png.bitPos_lt_8_writeBits bw bits len hbit)
    Png.decodeCompressedBlock spec.litLenTable spec.distTable br0
      ByteArray.empty = some (brAfter, raw) := by
  intro source spec litLenCodes distCodes bits len bwAll br0 brAfter
  have hdecode :=
    decodeCompressedBlock_generatedDynamicPayloadLz77_readerAt_writeBits
      (source := source) (raw := raw)
      (hvalid := by
        simpa [source] using deflateTokensLz77_fixed_valid raw)
      (hexpand := by
        simpa [source] using lz77TokensExpandList_deflateTokensLz77 raw)
      (bw := bw) hbit hcur
  simpa [source, spec, litLenCodes, distCodes, bits, len, bwAll, br0,
    brAfter] using hdecode

/-- Proof-facing name for the code-length array advertised by the generated
dynamic LZ77 header. It mirrors the local `lengths` binding in the writer. -/
def generatedDynamicHeaderCodeLengthsLz77
    (source : Array Png.Lz77Token) : Array Nat :=
  let litLenLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  let litLenCount := Png.generatedDynamicLitLenCount litLenLengths
  let distCount := Png.generatedDynamicDistCount distLengths
  (litLenLengths.extract 0 litLenCount) ++
    (distLengths.extract 0 distCount)

/-- Every generated LZ77 header code-length entry is a valid DEFLATE code
length. This supplies the header writer replay with bounded literal tokens. -/
lemma generatedDynamicHeaderCodeLengthsLz77_entries_le_15
    (source : Array Png.Lz77Token) :
    ArrayEntriesLe (generatedDynamicHeaderCodeLengthsLz77 source) 15 := by
  unfold generatedDynamicHeaderCodeLengthsLz77
  apply arrayEntriesLe_append
  · apply arrayEntriesLe_extract
    exact generatedDynamicLitLenLengths_entries_le_15
      (Png.litLenSymbolFreqsLz77 source)
  · apply arrayEntriesLe_extract
    exact generatedDynamicDistLengthsLz77_entries_le_15
      (Png.distSymbolFreqsLz77 source)

/-- The generated LZ77 header code-length buffer is the full literal/length
table followed by the full v1 30-symbol distance table. This is parser
bookkeeping for generated full dynamic headers. -/
lemma generatedDynamicHeaderCodeLengthsLz77_eq_full
    (source : Array Png.Lz77Token) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    generatedDynamicHeaderCodeLengthsLz77 source = litLenLengths ++ distLengths := by
  intro litLenLengths distLengths
  have hlitSize : litLenLengths.size = 286 := by
    simp [litLenLengths, generatedDynamicLitLenLengths_size,
      litLenSymbolFreqsLz77_size]
  have hdistSize : distLengths.size = 30 := by
    simpa [distLengths] using
      generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
  have hlitExtract :
      litLenLengths.extract 0 286 = litLenLengths := by
    rw [← hlitSize]
    exact array_extract_zero_size litLenLengths
  have hdistExtract :
      distLengths.extract 0 30 = distLengths := by
    rw [← hdistSize]
    exact array_extract_zero_size distLengths
  simp [generatedDynamicHeaderCodeLengthsLz77, litLenLengths, distLengths,
    Png.generatedDynamicLitLenCount, Png.generatedDynamicDistCount,
    hlitExtract, hdistExtract]

/-- The generated LZ77 header buffer contains exactly the parser's full
literal/length and distance entry count. This feeds the length-size check in
dynamic table reconstruction. -/
lemma generatedDynamicHeaderCodeLengthsLz77_size_full
    (source : Array Png.Lz77Token) :
    (generatedDynamicHeaderCodeLengthsLz77 source).size = 286 + 30 := by
  let litLenLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  have hfull :
      generatedDynamicHeaderCodeLengthsLz77 source = litLenLengths ++ distLengths := by
    simpa [litLenLengths, distLengths] using
      generatedDynamicHeaderCodeLengthsLz77_eq_full source
  have hlitSize : litLenLengths.size = 286 := by
    simp [litLenLengths, generatedDynamicLitLenLengths_size,
      litLenSymbolFreqsLz77_size]
  have hdistSize : distLengths.size = 30 := by
    simpa [distLengths] using
      generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
  simp [hfull, hlitSize, hdistSize]

/-- Extracting the literal/length prefix from the generated LZ77 header buffer
recovers the generated literal/length table. This matches the parser's `HLIT`
split for full generated headers. -/
lemma generatedDynamicHeaderCodeLengthsLz77_extract_lit_full
    (source : Array Png.Lz77Token) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    (generatedDynamicHeaderCodeLengthsLz77 source).extract 0 286 =
      litLenLengths := by
  intro litLenLengths
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  have hfull :
      generatedDynamicHeaderCodeLengthsLz77 source = litLenLengths ++ distLengths := by
    simpa [litLenLengths, distLengths] using
      generatedDynamicHeaderCodeLengthsLz77_eq_full source
  have hlitSize : litLenLengths.size = 286 := by
    simp [litLenLengths, generatedDynamicLitLenLengths_size,
      litLenSymbolFreqsLz77_size]
  rw [hfull]
  simp [hlitSize]

/-- Extracting the distance suffix from the generated LZ77 header buffer
recovers the generated v1 distance table. This matches the parser's `HDIST`
split for full generated headers. -/
lemma generatedDynamicHeaderCodeLengthsLz77_extract_dist_full
    (source : Array Png.Lz77Token) :
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    (generatedDynamicHeaderCodeLengthsLz77 source).extract 286 (286 + 30) =
      distLengths := by
  intro distLengths
  let litLenLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  have hfull :
      generatedDynamicHeaderCodeLengthsLz77 source = litLenLengths ++ distLengths := by
    simpa [litLenLengths, distLengths] using
      generatedDynamicHeaderCodeLengthsLz77_eq_full source
  have hlitSize : litLenLengths.size = 286 := by
    simp [litLenLengths, generatedDynamicLitLenLengths_size,
      litLenSymbolFreqsLz77_size]
  have hdistSize : distLengths.size = 30 := by
    simpa [distLengths] using
      generatedDynamicDistLengthsLz77_size (Png.distSymbolFreqsLz77 source)
  rw [hfull]
  simp [hlitSize, hdistSize]

/-- The generated LZ77 dynamic header writer is its fixed prefix followed by
the literal code-length token stream for the advertised length tables. -/
lemma writeGeneratedDynamicHeaderLz77_eq_prefix_writeBits
    (bw : Png.BitWriter) (source : Array Png.Lz77Token) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    Png.writeGeneratedDynamicHeader bw litLenLengths distLengths =
      Png.BitWriter.writeBits
        (Png.BitWriter.writeBits bw prefixBits Png.generatedDynamicHeaderPrefixLen)
        (codeLenTokenStreamBits codeTokens.toList)
        (codeLenTokenStreamLen codeTokens.toList) := by
  intro litLenLengths distLengths lengths codeTokens prefixBits
  have hlengths : ArrayEntriesLe lengths 15 := by
    simpa [lengths] using
      generatedDynamicHeaderCodeLengthsLz77_entries_le_15 source
  have htail :=
    writeDynamicCodeLengths_generated_eq_writeBits
      (bw := Png.BitWriter.writeBits bw prefixBits Png.generatedDynamicHeaderPrefixLen)
      (lengths := lengths) hlengths
  simpa [Png.writeGeneratedDynamicHeader, litLenLengths, distLengths, lengths,
    codeTokens, prefixBits, generatedDynamicHeaderCodeLengthsLz77] using htail

/-- The generated LZ77 dynamic header writer is equivalent to one packed bit
stream. This normal form lets later proofs concatenate header and payload. -/
lemma writeGeneratedDynamicHeaderLz77_eq_writeBits
    (bw : Png.BitWriter) (source : Array Png.Lz77Token) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    Png.writeGeneratedDynamicHeader bw litLenLengths distLengths =
      Png.BitWriter.writeBits bw
        (prefixBits |||
          (codeLenTokenStreamBits codeTokens.toList <<<
            Png.generatedDynamicHeaderPrefixLen))
        (Png.generatedDynamicHeaderPrefixLen +
          codeLenTokenStreamLen codeTokens.toList) := by
  intro litLenLengths distLengths lengths codeTokens prefixBits
  have hprefix :=
    writeGeneratedDynamicHeaderLz77_eq_prefix_writeBits
      (bw := bw) (source := source)
  have hprefixBits :
      prefixBits < 2 ^ Png.generatedDynamicHeaderPrefixLen := by
    simpa [prefixBits, Png.generatedDynamicLitLenCount,
      Png.generatedDynamicDistCount] using
      (show Png.generatedDynamicHeaderPrefixBits 286 30 <
          2 ^ Png.generatedDynamicHeaderPrefixLen by
        native_decide)
  have hconcat :=
    Png.writeBits_concat bw prefixBits
      (codeLenTokenStreamBits codeTokens.toList)
      Png.generatedDynamicHeaderPrefixLen
      (codeLenTokenStreamLen codeTokens.toList)
      hprefixBits
  simpa [litLenLengths, distLengths, lengths, codeTokens, prefixBits]
    using hprefix.trans hconcat.symm

/-- The packed generated LZ77 dynamic header fits in its advertised width.
This is the code-space bound needed when appending the payload bits. -/
lemma generatedDynamicHeaderBitsLz77_lt_codeSpace
    (source : Array Png.Lz77Token) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    headerBits < 2 ^ headerLen := by
  intro litLenLengths distLengths lengths codeTokens prefixBits headerBits headerLen
  have hvalid : ∀ token ∈ codeTokens.toList, CodeLenTokenValid token := by
    exact codeLenTokensValid_toList
      (by
        simpa [lengths, codeTokens] using
          codeLenLiteralTokensOfLengths_valid lengths
            (by
              simpa [lengths] using
                generatedDynamicHeaderCodeLengthsLz77_entries_le_15 source))
  have hprefixBits :
      prefixBits < 2 ^ Png.generatedDynamicHeaderPrefixLen := by
    simpa [prefixBits, Png.generatedDynamicLitLenCount,
      Png.generatedDynamicDistCount] using
      (show Png.generatedDynamicHeaderPrefixBits 286 30 <
          2 ^ Png.generatedDynamicHeaderPrefixLen by
        native_decide)
  have htokenBits :
      codeLenTokenStreamBits codeTokens.toList <
        2 ^ codeLenTokenStreamLen codeTokens.toList :=
    codeLenTokenStreamBits_lt_codeSpace codeTokens.toList hvalid
  have htokenShift :
      codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen <
        2 ^ headerLen := by
    rw [Nat.shiftLeft_eq]
    have hmul :
        codeLenTokenStreamBits codeTokens.toList *
            2 ^ Png.generatedDynamicHeaderPrefixLen <
          2 ^ codeLenTokenStreamLen codeTokens.toList *
            2 ^ Png.generatedDynamicHeaderPrefixLen :=
      (Nat.mul_lt_mul_right
        (Nat.two_pow_pos Png.generatedDynamicHeaderPrefixLen)).mpr htokenBits
    simpa [headerLen, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul
  have hprefixWide :
      prefixBits < 2 ^ headerLen := by
    exact lt_of_lt_of_le hprefixBits
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by
        simp [headerLen]))
  simpa [headerBits] using Nat.or_lt_two_pow hprefixWide htokenShift

/-- Writing arbitrary suffix bits after the generated LZ77 dynamic header is
the same as writing one packed header-plus-suffix stream. -/
lemma writeGeneratedDynamicHeaderLz77_rest_eq_writeBits
    (bw : Png.BitWriter) (source : Array Png.Lz77Token)
    (restBits restLen : Nat) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    Png.BitWriter.writeBits
        (Png.writeGeneratedDynamicHeader bw litLenLengths distLengths)
        restBits restLen =
      Png.BitWriter.writeBits bw
        (headerBits ||| (restBits <<< headerLen))
        (headerLen + restLen) := by
  intro litLenLengths distLengths lengths codeTokens prefixBits headerBits headerLen
  have hheader :=
    writeGeneratedDynamicHeaderLz77_eq_writeBits (bw := bw) (source := source)
  have hheader' :
      Png.writeGeneratedDynamicHeader bw litLenLengths distLengths =
        Png.BitWriter.writeBits bw headerBits headerLen := by
    simpa [litLenLengths, distLengths, lengths, codeTokens, prefixBits,
      headerBits, headerLen] using hheader
  have hheaderBits :
      headerBits < 2 ^ headerLen := by
    simpa [litLenLengths, distLengths, lengths, codeTokens, prefixBits,
      headerBits, headerLen] using
      generatedDynamicHeaderBitsLz77_lt_codeSpace source
  have hconcat :=
    Png.writeBits_concat bw headerBits restBits headerLen restLen hheaderBits
  simpa [hheader', headerBits, headerLen] using hconcat.symm

/-- The public LZ77 dynamic encoder is its generated header followed by the
packed generated dynamic LZ77 payload bitstream. -/
lemma deflateDynamicLz77_eq_payloadBitsWriter (raw : ByteArray) :
    let source := Png.deflateTokensLz77 raw
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
    let distCodes := Png.canonicalRevCodesFromLengths distLengths
    let bw0 := Png.BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 2 2
    let bw3 := Png.writeGeneratedDynamicHeader bw2 litLenLengths distLengths
    let payloadBits :=
      dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let payloadLen :=
      dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    Png.deflateDynamicLz77 raw =
      (Png.BitWriter.writeBits bw3 payloadBits payloadLen).flush := by
  intro source litLenLengths distLengths litLenCodes distCodes bw0 bw1 bw2
    bw3 payloadBits payloadLen
  have hpayload :=
    writeDynamicPayloadLz77_deflateTokensLz77_eq_writeBits raw bw3
  have hpayload' :
      Png.writeDynamicPayloadLz77 bw3 source litLenCodes distCodes =
        Png.BitWriter.writeBits bw3 payloadBits payloadLen := by
    simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
      payloadBits, payloadLen] using hpayload
  simpa [Png.deflateDynamicLz77, source, litLenLengths, distLengths,
    litLenCodes, distCodes, bw0, bw1, bw2, bw3, payloadBits, payloadLen,
    hpayload']

/-- The public LZ77 dynamic encoder's generated header and payload collapse
to one packed suffix after the three-bit final-dynamic block tag. -/
lemma deflateDynamicLz77_eq_blockSuffixWriter (raw : ByteArray) :
    let source := Png.deflateTokensLz77 raw
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
    let distCodes := Png.canonicalRevCodesFromLengths distLengths
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    let payloadBits :=
      dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let payloadLen :=
      dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let suffixBits := headerBits ||| (payloadBits <<< headerLen)
    let suffixLen := headerLen + payloadLen
    let bw0 := Png.BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 2 2
    Png.deflateDynamicLz77 raw =
      (Png.BitWriter.writeBits bw2 suffixBits suffixLen).flush := by
  intro source litLenLengths distLengths litLenCodes distCodes lengths
    codeTokens prefixBits headerBits headerLen payloadBits payloadLen
    suffixBits suffixLen bw0 bw1 bw2
  have hpayload :=
    deflateDynamicLz77_eq_payloadBitsWriter raw
  have hrest :=
    writeGeneratedDynamicHeaderLz77_rest_eq_writeBits
      (bw := bw2) (source := source) (restBits := payloadBits)
      (restLen := payloadLen)
  have hrest' :
      Png.BitWriter.writeBits
          (Png.writeGeneratedDynamicHeader bw2 litLenLengths distLengths)
          payloadBits payloadLen =
        Png.BitWriter.writeBits bw2 suffixBits suffixLen := by
    simpa [source, litLenLengths, distLengths, lengths, codeTokens,
      prefixBits, headerBits, headerLen, payloadBits, payloadLen,
      suffixBits, suffixLen] using hrest
  simpa [source, litLenLengths, distLengths, litLenCodes, distCodes, bw0,
    bw1, bw2, payloadBits, payloadLen, suffixBits, suffixLen, hrest']
    using hpayload

/-- The public LZ77 dynamic encoder is one packed final dynamic block
bitstream. This is the writer shape needed by top-level decode proofs. -/
lemma deflateDynamicLz77_eq_collapsedWriter (raw : ByteArray) :
    let source := Png.deflateTokensLz77 raw
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
    let distCodes := Png.canonicalRevCodesFromLengths distLengths
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    let payloadBits :=
      dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let payloadLen :=
      dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let suffixBits := headerBits ||| (payloadBits <<< headerLen)
    let suffixLen := headerLen + payloadLen
    let streamBitsFull := 5 ||| (suffixBits <<< 3)
    let streamLenFull := 3 + suffixLen
    Png.deflateDynamicLz77 raw =
      (Png.BitWriter.writeBits Png.BitWriter.empty
        streamBitsFull streamLenFull).flush := by
  intro source litLenLengths distLengths litLenCodes distCodes lengths
    codeTokens prefixBits headerBits headerLen payloadBits payloadLen
    suffixBits suffixLen streamBitsFull streamLenFull
  let bw0 := Png.BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 2 2
  have hblock :=
    deflateDynamicLz77_eq_blockSuffixWriter raw
  have htag :
      bw2 = Png.BitWriter.writeBits bw0 5 3 := by
    have h :=
      Png.writeBits_concat bw0 1 2 1 2 (by decide : 1 < 2 ^ 1)
    simpa [bw0, bw1, bw2, Nat.add_comm] using h.symm
  have hcollapse :
      Png.BitWriter.writeBits bw2 suffixBits suffixLen =
        Png.BitWriter.writeBits Png.BitWriter.empty
          streamBitsFull streamLenFull := by
    have h :=
      Png.writeBits_concat Png.BitWriter.empty 5 suffixBits 3 suffixLen
        (by decide : 5 < 2 ^ 3)
    simpa [bw0, htag, streamBitsFull, streamLenFull] using h.symm
  calc
    Png.deflateDynamicLz77 raw =
        (Png.BitWriter.writeBits bw2 suffixBits suffixLen).flush := by
          simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
            lengths, codeTokens, prefixBits, headerBits, headerLen,
            payloadBits, payloadLen, suffixBits, suffixLen, bw0, bw1, bw2]
            using hblock
    _ = (Png.BitWriter.writeBits Png.BitWriter.empty
          streamBitsFull streamLenFull).flush := by
          simp [hcollapse]

/-- Splits the packed generated LZ77 dynamic suffix at the generated-header
boundary. The block proof uses this to reuse the payload decoder theorem after
the runtime header parser has advanced to the payload start. -/
lemma generatedDynamicPayloadLz77PrefixWriter_eq_suffixWriter
    (source : Array Png.Lz77Token) (hdrHeader : Png.BitWriter) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
    let distCodes := Png.canonicalRevCodesFromLengths distLengths
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    let payloadBits :=
      dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let payloadLen :=
      dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let suffixBits := headerBits ||| (payloadBits <<< headerLen)
    let suffixLen := headerLen + payloadLen
    let bwPayloadStart :=
      Png.BitWriter.writeBits hdrHeader suffixBits headerLen
    let bwPayloadAll :=
      Png.BitWriter.writeBits bwPayloadStart payloadBits payloadLen
    let suffixWriter :=
      Png.BitWriter.writeBits hdrHeader suffixBits suffixLen
    bwPayloadAll = suffixWriter := by
  intro litLenLengths distLengths litLenCodes distCodes lengths codeTokens
    prefixBits headerBits headerLen payloadBits payloadLen suffixBits
    suffixLen bwPayloadStart bwPayloadAll suffixWriter
  have hheaderBits :
      headerBits < 2 ^ headerLen := by
    simpa [litLenLengths, distLengths, lengths, codeTokens, prefixBits,
      headerBits, headerLen] using
      generatedDynamicHeaderBitsLz77_lt_codeSpace source
  have hprefix :
      bwPayloadStart =
        Png.BitWriter.writeBits hdrHeader headerBits headerLen := by
    simpa [bwPayloadStart, suffixBits] using
      Png.writeBits_or_shift_tail hdrHeader headerBits payloadBits
        headerLen hheaderBits
  have hconcat :=
    Png.writeBits_concat hdrHeader headerBits payloadBits headerLen
      payloadLen hheaderBits
  simpa [bwPayloadAll, bwPayloadStart, suffixWriter, suffixBits, suffixLen,
    hprefix] using hconcat.symm

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Replays the generated LZ77 header's literal code-length token stream with
any runtime fuel large enough for the generated tokens and completion check.
This is the length-reader bridge used by the dynamic-table parser. -/
lemma readDynamicTablesLengthsFuel_generatedHeaderLz77LiteralAnyFuel_readerAt_writeBits
    (bw : Png.BitWriter) (source : Array Png.Lz77Token)
    (fuel restBits restLen : Nat)
    (hfuel :
      (Png.codeLenLiteralTokensOfLengths
        (generatedDynamicHeaderCodeLengthsLz77 source)).toList.length + 1 ≤ fuel)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let bitsTot := codeLenTokenStreamBits codeTokens.toList |||
      (restBits <<< codeLenTokenStreamLen codeTokens.toList)
    let lenTot := codeLenTokenStreamLen codeTokens.toList + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot
        (codeLenTokenStreamLen codeTokens.toList))
      bw'.flush
      (by
        have hk : codeLenTokenStreamLen codeTokens.toList ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot
            (codeLenTokenStreamLen codeTokens.toList) lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot
        (codeLenTokenStreamLen codeTokens.toList) hbit)
    Png.readDynamicTablesLengthsFuel fuel lengths.size
        generatedCodeLenHuffman br #[] =
      some (lengths, brAfter) := by
  intro lengths codeTokens bitsTot lenTot bw' br brAfter
  have hvalid : ∀ token ∈ codeTokens.toList, CodeLenTokenValid token := by
    exact codeLenTokensValid_toList
      (by
        simpa [lengths, codeTokens] using
          codeLenLiteralTokensOfLengths_valid lengths
            (by
              simpa [lengths] using
                generatedDynamicHeaderCodeLengthsLz77_entries_le_15 source))
  have hexpand :
      codeLenTokensExpandList? codeTokens.toList #[] = some lengths := by
    simpa [lengths, codeTokens] using
      codeLenLiteralTokensOfLengths_expandList lengths
  have hcount :
      codeLenTokenListOutputCount codeTokens.toList = lengths.size := by
    simpa [codeTokens] using
      codeLenLiteralTokensOfLengths_outputCount lengths
  have hfuel' : codeTokens.toList.length + 1 ≤ fuel := by
    simpa [lengths, codeTokens] using hfuel
  have hcore :=
    readDynamicTablesLengthsFuel_codeLenTokenStream_anyFuel_readerAt_writeBits
      (bw := bw) (tokens := codeTokens.toList)
      (fuel := fuel) (restBits := restBits) (restLen := restLen)
      (lengths := #[]) (lengths' := lengths)
      hvalid hexpand hfuel' hbit hcur
  simpa [bitsTot, lenTot, bw', br, brAfter, hcount]
    using hcore

/-- Proof-local mirror of the parser tail after the generated code-length-code
table has been read for an LZ77 generated header. It fixes the full 286+30
shape before rebuilding the literal/length and distance tables. -/
private def finishGeneratedDynamicTablesAfterCodeLenLengthsLz77
    (br : Png.BitReader) : Option (Png.Huffman × Png.Huffman × Png.BitReader) := do
  let total := 286 + 30
  let lengths0 : Array Nat := Array.mkEmpty total
  let (lengths, brNext) ←
    Png.readDynamicTablesLengthsFuel (br.data.size * 8 + 1)
      total generatedCodeLenHuffman br lengths0
  if lengths.size != total then
    none
  let litLenLengths := lengths.extract 0 286
  let distLengths := lengths.extract 286 (286 + 30)
  let litLenTable ← Png.mkHuffman litLenLengths
  let distTable ← Png.buildDynamicDistTable distLengths
  return (litLenTable, distTable, brNext)

/-- Proof-local mirror of `readDynamicTables` after `HLIT`, `HDIST`, and
`HCLEN` have been read for an LZ77 generated header. -/
private def readGeneratedDynamicTablesAfterHeaderLz77
    (br : Png.BitReader) : Option (Png.Huffman × Png.Huffman × Png.BitReader) := do
  let r ←
    forIn (List.range' 0 Png.codeLenOrder.size)
        ((⟨br, Array.replicate 19 0⟩ : MProd Png.BitReader (Array Nat)))
        (fun i r =>
          if h : r.fst.bitIndex + 3 ≤ r.fst.data.size * 8 then
            some
              (ForInStep.yield
                ⟨(r.fst.readBits 3 h).snd,
                  r.snd.setIfInBounds Png.codeLenOrder[i]! (r.fst.readBits 3 h).fst⟩)
          else
            none)
  let brCur := r.fst
  let codeLenLengths := r.snd
  let codeLenTable ← Png.mkHuffman codeLenLengths
  let total := 286 + 30
  let lengths0 : Array Nat := Array.mkEmpty total
  let (lengths, brNext) ←
    Png.readDynamicTablesLengthsFuel (brCur.data.size * 8 + 1)
      total codeLenTable brCur lengths0
  if lengths.size != total then
    none
  let litLenLengths := lengths.extract 0 286
  let distLengths := lengths.extract 286 (286 + 30)
  let litLenTable ← Png.mkHuffman litLenLengths
  let distTable ← Png.buildDynamicDistTable distLengths
  return (litLenTable, distTable, brNext)

/-- Once the generated LZ77 code-length-code table has been replayed, the
after-header parser mirror reduces to the generated LZ77 parser tail. -/
private lemma readGeneratedDynamicTablesAfterHeaderLz77_eq_finish
    {br brNext : Png.BitReader}
    (hread :
      readGeneratedCodeLenLengths19 br =
        some (generatedCodeLenLengthsFilled, brNext))
    (hmk :
      Png.mkHuffman generatedCodeLenLengthsFilled =
        some generatedCodeLenHuffman) :
    readGeneratedDynamicTablesAfterHeaderLz77 br =
      finishGeneratedDynamicTablesAfterCodeLenLengthsLz77 brNext := by
  unfold readGeneratedDynamicTablesAfterHeaderLz77
    finishGeneratedDynamicTablesAfterCodeLenLengthsLz77
  rw [readGeneratedCodeLenLengths19_eq_forIn_mprod br]
  simp [hread, hmk]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Replays the generated LZ77 parser tail after the helper code-length-code
table has been reconstructed. It proves the generic dynamic table builder
recovers the generated LZ77 literal/length and distance tables. -/
lemma finishGeneratedDynamicTablesAfterCodeLenLengthsLz77_readerAt_writeBits
    (bw : Png.BitWriter) (source : Array Png.Lz77Token)
    (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let bitsTot := codeLenTokenStreamBits codeTokens.toList |||
      (restBits <<< codeLenTokenStreamLen codeTokens.toList)
    let lenTot := codeLenTokenStreamLen codeTokens.toList + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot
        (codeLenTokenStreamLen codeTokens.toList))
      bw'.flush
      (by
        have hk : codeLenTokenStreamLen codeTokens.toList ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot
            (codeLenTokenStreamLen codeTokens.toList) lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot
        (codeLenTokenStreamLen codeTokens.toList) hbit)
    finishGeneratedDynamicTablesAfterCodeLenLengthsLz77 br =
      some ((generatedDynamicTableSpecLz77 source).litLenTable,
        (generatedDynamicTableSpecLz77 source).distTable, brAfter) := by
  intro lengths codeTokens bitsTot lenTot bw' br brAfter
  let litLenLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  have hlitMk :
      Png.mkHuffman litLenLengths =
        some (generatedDynamicTableSpecLz77 source).litLenTable := by
    simpa [generatedDynamicTableSpecLz77, litLenLengths] using
      mkHuffman_generatedDynamicLitLenLengthsLz77_eq source
  have hdistBuild :
      Png.buildDynamicDistTable distLengths =
        some (generatedDynamicTableSpecLz77 source).distTable := by
    simpa [generatedDynamicTableSpecLz77, distLengths] using
      buildDynamicDistTable_generatedDynamicDistLengthsLz77_eq
        (Png.distSymbolFreqsLz77 source)
  have hlengthsSize : lengths.size = 286 + 30 := by
    simpa [lengths] using
      generatedDynamicHeaderCodeLengthsLz77_size_full source
  have hlitExtract : lengths.extract 0 286 = litLenLengths := by
    simpa [lengths, litLenLengths] using
      generatedDynamicHeaderCodeLengthsLz77_extract_lit_full source
  have hdistExtract : lengths.extract 286 (286 + 30) = distLengths := by
    simpa [lengths, distLengths] using
      generatedDynamicHeaderCodeLengthsLz77_extract_dist_full source
  have hfuel : codeTokens.toList.length + 1 ≤ br.data.size * 8 + 1 := by
    have hflush :
        bw'.flush.size * 8 ≥ bw'.bitCount := by
      exact Png.flush_size_mul_ge_bitCount (bw := bw')
        (hbit := Png.bitPos_lt_8_writeBits bw bitsTot lenTot hbit)
    have hcount :
        codeTokens.toList.length ≤ bw'.bitCount := by
      have htokens :=
        codeLenTokenStreamLen_ge_length codeTokens.toList
      have htokensArray :
          codeTokens.size ≤ codeLenTokenStreamLen codeTokens.toList := by
        simpa using htokens
      rw [Png.bitCount_writeBits]
      simp [bw', lenTot]
      omega
    have hdata : br.data.size = bw'.flush.size := by
      rfl
    have hsize : codeTokens.toList.length ≤ br.data.size * 8 := by
      calc
        codeTokens.toList.length ≤ bw'.bitCount := hcount
        _ ≤ bw'.flush.size * 8 := by omega
        _ = br.data.size * 8 := by simp [hdata]
    exact Nat.succ_le_succ hsize
  have hreadLengths :=
    readDynamicTablesLengthsFuel_generatedHeaderLz77LiteralAnyFuel_readerAt_writeBits
      (bw := bw) (source := source) (fuel := br.data.size * 8 + 1)
      (restBits := restBits) (restLen := restLen)
      (by simpa [lengths, codeTokens] using hfuel) hbit hcur
  have hreadLengths' :
      Png.readDynamicTablesLengthsFuel (br.data.size * 8 + 1)
          (286 + 30) generatedCodeLenHuffman br #[] =
        some (lengths, brAfter) := by
    simpa [litLenLengths, distLengths, lengths, codeTokens, bitsTot, lenTot,
      bw', br, brAfter, hlengthsSize] using hreadLengths
  unfold finishGeneratedDynamicTablesAfterCodeLenLengthsLz77
  dsimp
  rw [hreadLengths']
  simp [Option.bind, hlengthsSize, hlitExtract, hdistExtract, hlitMk,
    hdistBuild]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Replays the generated LZ77 after-header parser from the reader positioned
after `HLIT`, `HDIST`, and `HCLEN`. It consumes the all-five helper table,
then the generated LZ77 literal code-length stream. -/
lemma readGeneratedDynamicTablesAfterHeaderLz77_readerAt_writeBits
    (bw : Png.BitWriter) (source : Array Png.Lz77Token)
    (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let codeBits := codeLenTokenStreamBits codeTokens.toList
    let codeLen := codeLenTokenStreamLen codeTokens.toList
    let restAfterPrefixBits := codeBits ||| (restBits <<< codeLen)
    let restAfterPrefixLen := codeLen + restLen
    let prefixBits := Png.generatedDynamicHeaderPrefixBits 286 30
    let bitsTot := prefixBits |||
      (restAfterPrefixBits <<< Png.generatedDynamicHeaderPrefixLen)
    let lenTot := Png.generatedDynamicHeaderPrefixLen + restAfterPrefixLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br14 := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot 14) bw'.flush
      (by
        have hk : 14 ≤ lenTot := by
          have hprefix : 14 ≤ Png.generatedDynamicHeaderPrefixLen :=
            generatedDynamicHeaderPrefixLen_ge_14
          omega
        simpa [bw', lenTot] using
          Png.flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
      (Png.bitPos_lt_8_writeBits bw bitsTot 14 hbit)
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot
        (Png.generatedDynamicHeaderPrefixLen + codeLen))
      bw'.flush
      (by
        have hk : Png.generatedDynamicHeaderPrefixLen + codeLen ≤ lenTot := by
          simp [lenTot, restAfterPrefixLen]
        simpa [bw', lenTot] using
          Png.flush_size_writeBits_prefix bw bitsTot
            (Png.generatedDynamicHeaderPrefixLen + codeLen) lenTot hk)
      (Png.bitPos_lt_8_writeBits bw bitsTot
        (Png.generatedDynamicHeaderPrefixLen + codeLen) hbit)
    readGeneratedDynamicTablesAfterHeaderLz77 br14 =
      some ((generatedDynamicTableSpecLz77 source).litLenTable,
        (generatedDynamicTableSpecLz77 source).distTable, brAfter) := by
  intro lengths codeTokens codeBits codeLen
    restAfterPrefixBits restAfterPrefixLen prefixBits bitsTot lenTot bw' br14 brAfter
  let bwPrefix :=
    Png.BitWriter.writeBits bw bitsTot Png.generatedDynamicHeaderPrefixLen
  let bwTail := Png.BitWriter.writeBits bwPrefix restAfterPrefixBits restAfterPrefixLen
  let brAfterPrefix := Png.BitWriter.readerAt bwPrefix bw'.flush
    (by
      have hk : Png.generatedDynamicHeaderPrefixLen ≤ lenTot := by
        simp [lenTot]
      simpa [bw', lenTot, bwPrefix] using
        Png.flush_size_writeBits_prefix bw bitsTot
          Png.generatedDynamicHeaderPrefixLen lenTot hk)
    (Png.bitPos_lt_8_writeBits bw bitsTot
      Png.generatedDynamicHeaderPrefixLen hbit)
  have hprefixBits :
      prefixBits < 2 ^ Png.generatedDynamicHeaderPrefixLen := by
    simpa [prefixBits] using
      (show Png.generatedDynamicHeaderPrefixBits 286 30 <
          2 ^ Png.generatedDynamicHeaderPrefixLen by
        native_decide)
  have hprefixWriter :
      bwPrefix = Png.BitWriter.writeBits bw prefixBits
          Png.generatedDynamicHeaderPrefixLen := by
    simpa [bwPrefix, bitsTot] using
      (Png.writeBits_or_shift_tail
        (bw := bw) (bits := prefixBits) (tailBits := restAfterPrefixBits)
        (len := Png.generatedDynamicHeaderPrefixLen) hprefixBits)
  have hbwTail : bw' = bwTail := by
    have hconcat :=
      Png.writeBits_concat bw prefixBits restAfterPrefixBits
        Png.generatedDynamicHeaderPrefixLen restAfterPrefixLen hprefixBits
    simpa [bw', bwTail, bitsTot, lenTot, bwPrefix, hprefixWriter]
      using hconcat
  have htailFlush : bw'.flush = bwTail.flush := congrArg Png.BitWriter.flush hbwTail
  have hreadCodeLenRaw :=
    readGeneratedCodeLenLengths19_readerAt_writeBits
      (bw := bw) (restBits := restAfterPrefixBits)
      (restLen := restAfterPrefixLen) hbit hcur
  have hreadCodeLen :
      readGeneratedCodeLenLengths19 br14 =
        some (generatedCodeLenLengthsFilled, brAfterPrefix) := by
    simpa [generatedCodeLenReaderAt, br14, brAfterPrefix, prefixBits, bitsTot,
      lenTot, bw', bwPrefix, generatedDynamicHeaderPrefixLen_eq,
      codeLenOrder_size, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hreadCodeLenRaw
  have hbitPrefix : bwPrefix.bitPos < 8 := by
    exact Png.bitPos_lt_8_writeBits bw bitsTot
      Png.generatedDynamicHeaderPrefixLen hbit
  have hcurPrefix : bwPrefix.curClearAbove := by
    exact Png.curClearAbove_writeBits bw bitsTot
      Png.generatedDynamicHeaderPrefixLen hbit hcur
  have hfinish :=
    finishGeneratedDynamicTablesAfterCodeLenLengthsLz77_readerAt_writeBits
      (bw := bwPrefix) (source := source)
      (restBits := restBits) (restLen := restLen)
      hbitPrefix hcurPrefix
  let brFinish := Png.BitWriter.readerAt bwPrefix bwTail.flush
    (Png.flush_size_writeBits_le bwPrefix restAfterPrefixBits restAfterPrefixLen)
    hbitPrefix
  let brAfterFinish := Png.BitWriter.readerAt
    (Png.BitWriter.writeBits bwPrefix restAfterPrefixBits codeLen)
    bwTail.flush
    (by
      have hk : codeLen ≤ restAfterPrefixLen := by
        simp [restAfterPrefixLen]
      simpa [bwTail, restAfterPrefixLen, codeLen, restAfterPrefixBits] using
        Png.flush_size_writeBits_prefix bwPrefix restAfterPrefixBits
          codeLen restAfterPrefixLen hk)
    (Png.bitPos_lt_8_writeBits bwPrefix restAfterPrefixBits codeLen hbitPrefix)
  have hbrFinishEq : brAfterPrefix = brFinish := by
    refine readerAt_eq_of_eqs_generated rfl htailFlush _ _ _ _
  have hshiftTail : bitsTot >>> Png.generatedDynamicHeaderPrefixLen =
      restAfterPrefixBits := by
    simpa [bitsTot] using
      (Png.shiftRight_or_shiftLeft prefixBits restAfterPrefixBits
        Png.generatedDynamicHeaderPrefixLen hprefixBits)
  have hafterWriter :
      Png.BitWriter.writeBits bwPrefix restAfterPrefixBits codeLen =
        Png.BitWriter.writeBits bw bitsTot
          (Png.generatedDynamicHeaderPrefixLen + codeLen) := by
    have hsplit :=
      Png.writeBits_split bw bitsTot Png.generatedDynamicHeaderPrefixLen codeLen
    simpa [bwPrefix, hshiftTail] using hsplit.symm
  have hbrAfterEq : brAfterFinish = brAfter := by
    refine readerAt_eq_of_eqs_generated hafterWriter htailFlush.symm _ _ _ _
  have hafterHeader :
      readGeneratedDynamicTablesAfterHeaderLz77 br14 =
        finishGeneratedDynamicTablesAfterCodeLenLengthsLz77 brAfterPrefix :=
    readGeneratedDynamicTablesAfterHeaderLz77_eq_finish
      hreadCodeLen mkHuffman_generatedCodeLenLengthsFilled_eq
  have hfinish' :
      finishGeneratedDynamicTablesAfterCodeLenLengthsLz77 brAfterPrefix =
        some ((generatedDynamicTableSpecLz77 source).litLenTable,
          (generatedDynamicTableSpecLz77 source).distTable, brAfter) := by
    rw [hbrFinishEq]
    simpa [lengths, codeTokens, codeBits, codeLen,
      restAfterPrefixBits, restAfterPrefixLen, bwTail, brFinish,
      brAfterFinish, hbrAfterEq] using hfinish
  rw [hafterHeader]
  exact hfinish'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Replays the full generic dynamic-table parser on the generated LZ77
dynamic header stream. This is the parser boundary before payload decoding. -/
lemma readDynamicTables_generatedHeaderLz77_readerAt_writeBits
    (bw : Png.BitWriter) (source : Array Png.Lz77Token)
    (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let codeBits := codeLenTokenStreamBits codeTokens.toList
    let codeLen := codeLenTokenStreamLen codeTokens.toList
    let restAfterPrefixBits := codeBits ||| (restBits <<< codeLen)
    let restAfterPrefixLen := codeLen + restLen
    let prefixBits := Png.generatedDynamicHeaderPrefixBits 286 30
    let bitsTot := prefixBits |||
      (restAfterPrefixBits <<< Png.generatedDynamicHeaderPrefixLen)
    let lenTot := Png.generatedDynamicHeaderPrefixLen + restAfterPrefixLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot
        (Png.generatedDynamicHeaderPrefixLen + codeLen))
      bw'.flush
      (by
        have hk : Png.generatedDynamicHeaderPrefixLen + codeLen ≤ lenTot := by
          simp [lenTot, restAfterPrefixLen]
        simpa [bw', lenTot] using
          Png.flush_size_writeBits_prefix bw bitsTot
            (Png.generatedDynamicHeaderPrefixLen + codeLen) lenTot hk)
      (Png.bitPos_lt_8_writeBits bw bitsTot
        (Png.generatedDynamicHeaderPrefixLen + codeLen) hbit)
    Png.readDynamicTables br =
      some ((generatedDynamicTableSpecLz77 source).litLenTable,
        (generatedDynamicTableSpecLz77 source).distTable, brAfter) := by
  intro lengths codeTokens codeBits codeLen
    restAfterPrefixBits restAfterPrefixLen prefixBits bitsTot lenTot bw' br brAfter
  let br5 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
    (by
      have hk : 5 ≤ lenTot := by
        have hprefix : 5 ≤ Png.generatedDynamicHeaderPrefixLen :=
          generatedDynamicHeaderPrefixLen_ge_5
        omega
      simpa [bw', lenTot] using
        Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk)
    (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  let br10 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 10) bw'.flush
    (by
      have hk : 10 ≤ lenTot := by
        have hprefix : 10 ≤ Png.generatedDynamicHeaderPrefixLen :=
          generatedDynamicHeaderPrefixLen_ge_10
        omega
      simpa [bw', lenTot] using
        Png.flush_size_writeBits_prefix bw bitsTot 10 lenTot hk)
    (Png.bitPos_lt_8_writeBits bw bitsTot 10 hbit)
  let br14 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 14) bw'.flush
    (by
      have hk : 14 ≤ lenTot := by
        have hprefix : 14 ≤ Png.generatedDynamicHeaderPrefixLen :=
          generatedDynamicHeaderPrefixLen_ge_14
        omega
      simpa [bw', lenTot] using
        Png.flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
    (Png.bitPos_lt_8_writeBits bw bitsTot 14 hbit)
  have hreadHlit :
      br.readBits 5
          (by
            have hk : 5 ≤ lenTot := by
              have hprefix : 5 ≤ Png.generatedDynamicHeaderPrefixLen :=
                generatedDynamicHeaderPrefixLen_ge_5
              omega
            simpa [br, bw', lenTot] using
              (Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot)
                (len := lenTot) (k := 5) hk hbit)) =
        (29, br5) := by
    simpa [prefixBits, bitsTot, lenTot, bw', br, br5]
      using
        readGeneratedDynamicHeader_hlit_readerAt_writeBits
          (bw := bw) (restBits := restAfterPrefixBits)
          (restLen := restAfterPrefixLen) hbit hcur
  have hreadHdist :
      br5.readBits 5
          (by
            have hk : 5 ≤ lenTot - 5 := by
              have hprefix : 5 ≤ Png.generatedDynamicHeaderPrefixLen - 5 :=
                generatedDynamicHeaderPrefixLen_sub5_ge_5
              omega
            simpa [br5, bw', lenTot] using
              (readerAt_writeBits_shift_bound_generated
                (bw := bw) (bits := bitsTot) (len := lenTot)
                (skip := 5) (k := 5)
                (by
                  have hprefix : 5 ≤ Png.generatedDynamicHeaderPrefixLen :=
                    generatedDynamicHeaderPrefixLen_ge_5
                  omega)
                hk hbit)) =
        (29, br10) := by
    simpa [prefixBits, bitsTot, lenTot, bw', br5, br10]
      using
        readGeneratedDynamicHeader_hdist_readerAt_writeBits
          (bw := bw) (restBits := restAfterPrefixBits)
          (restLen := restAfterPrefixLen) hbit hcur
  have hreadHclen :
      br10.readBits 4
          (by
            have hk : 4 ≤ lenTot - 10 := by
              have hprefix : 4 ≤ Png.generatedDynamicHeaderPrefixLen - 10 :=
                generatedDynamicHeaderPrefixLen_sub10_ge_4
              omega
            simpa [br10, bw', lenTot] using
              (readerAt_writeBits_shift_bound_generated
                (bw := bw) (bits := bitsTot) (len := lenTot)
                (skip := 10) (k := 4)
                (by
                  have hprefix : 10 ≤ Png.generatedDynamicHeaderPrefixLen :=
                    generatedDynamicHeaderPrefixLen_ge_10
                  omega)
                hk hbit)) =
        (15, br14) := by
    simpa [prefixBits, bitsTot, lenTot, bw', br10, br14]
      using
        readGeneratedDynamicHeader_hclen_readerAt_writeBits
          (bw := bw) (restBits := restAfterPrefixBits)
          (restLen := restAfterPrefixLen) hbit hcur
  have hafterHeader :=
    readGeneratedDynamicTablesAfterHeaderLz77_readerAt_writeBits
      (bw := bw) (source := source)
      (restBits := restBits) (restLen := restLen) hbit hcur
  have hcondHlit : br.bitIndex + 5 ≤ br.data.size * 8 := by
    have hk : 5 ≤ lenTot := by
      have hprefix : 5 ≤ Png.generatedDynamicHeaderPrefixLen :=
        generatedDynamicHeaderPrefixLen_ge_5
      omega
    simpa [br, bw', lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot)
        (len := lenTot) (k := 5) hk hbit)
  have hreadHlit' :
      br.readBits 5 hcondHlit = (29, br5) := by
    simpa [Png.readBits_proof_irrel] using hreadHlit
  have hcondHdist : br5.bitIndex + 5 ≤ br5.data.size * 8 := by
    have hk : 5 ≤ lenTot - 5 := by
      have hprefix : 5 ≤ Png.generatedDynamicHeaderPrefixLen - 5 :=
        generatedDynamicHeaderPrefixLen_sub5_ge_5
      omega
    simpa [br5, bw', lenTot] using
      (readerAt_writeBits_shift_bound_generated
        (bw := bw) (bits := bitsTot) (len := lenTot)
        (skip := 5) (k := 5)
        (by
          have hprefix : 5 ≤ Png.generatedDynamicHeaderPrefixLen :=
            generatedDynamicHeaderPrefixLen_ge_5
          omega)
        hk hbit)
  have hreadHdist' :
      br5.readBits 5 hcondHdist = (29, br10) := by
    simpa [Png.readBits_proof_irrel] using hreadHdist
  have hcondHclen : br10.bitIndex + 4 ≤ br10.data.size * 8 := by
    have hk : 4 ≤ lenTot - 10 := by
      have hprefix : 4 ≤ Png.generatedDynamicHeaderPrefixLen - 10 :=
        generatedDynamicHeaderPrefixLen_sub10_ge_4
      omega
    simpa [br10, bw', lenTot] using
      (readerAt_writeBits_shift_bound_generated
        (bw := bw) (bits := bitsTot) (len := lenTot)
        (skip := 10) (k := 4)
        (by
          have hprefix : 10 ≤ Png.generatedDynamicHeaderPrefixLen :=
            generatedDynamicHeaderPrefixLen_ge_10
          omega)
        hk hbit)
  have hreadHclen' :
      br10.readBits 4 hcondHclen = (15, br14) := by
    simpa [Png.readBits_proof_irrel] using hreadHclen
  unfold Png.readDynamicTables
  simp [hcondHlit, hreadHlit', hcondHdist, hreadHdist', hcondHclen,
    hreadHclen', Option.bind]
  simpa [readGeneratedDynamicTablesAfterHeaderLz77, readGeneratedCodeLenLengths19,
    Png.codeLenOrder, lengths, codeTokens,
    codeBits, codeLen, restAfterPrefixBits, restAfterPrefixLen, prefixBits,
    bitsTot, lenTot, bw', br14, brAfter, Option.bind] using hafterHeader

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Parses the generated LZ77 dynamic header from the packed suffix and lands
on the payload start. This connects `readDynamicTables` with the generated
LZ77 table package used by payload replay. -/
lemma readDynamicTables_generatedDynamicLz77Suffix_readerAt_writeBits
    (source : Array Png.Lz77Token) (hdrHeader : Png.BitWriter)
    (hbit : hdrHeader.bitPos < 8) (hcur : hdrHeader.curClearAbove) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
    let distCodes := Png.canonicalRevCodesFromLengths distLengths
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    let payloadBits :=
      dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let payloadLen :=
      dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let suffixBits := headerBits ||| (payloadBits <<< headerLen)
    let suffixLen := headerLen + payloadLen
    let suffixWriter :=
      Png.BitWriter.writeBits hdrHeader suffixBits suffixLen
    let streamReaderHeader := Png.BitWriter.readerAt hdrHeader
      suffixWriter.flush
      (Png.flush_size_writeBits_le hdrHeader suffixBits suffixLen)
      hbit
    let bwPayloadStart :=
      Png.BitWriter.writeBits hdrHeader suffixBits headerLen
    let brPayload := Png.BitWriter.readerAt bwPayloadStart
      suffixWriter.flush
      (by
        have hk : headerLen ≤ suffixLen := by omega
        simpa [bwPayloadStart, suffixWriter, suffixLen] using
          Png.flush_size_writeBits_prefix hdrHeader suffixBits
            headerLen suffixLen hk)
      (Png.bitPos_lt_8_writeBits hdrHeader suffixBits headerLen hbit)
    Png.readDynamicTables streamReaderHeader =
      some ((generatedDynamicTableSpecLz77 source).litLenTable,
        (generatedDynamicTableSpecLz77 source).distTable, brPayload) := by
  intro litLenLengths distLengths litLenCodes distCodes lengths codeTokens
    prefixBits headerBits headerLen payloadBits payloadLen suffixBits
    suffixLen suffixWriter streamReaderHeader bwPayloadStart brPayload
  have htables :=
    readDynamicTables_generatedHeaderLz77_readerAt_writeBits
      (bw := hdrHeader) (source := source)
      (restBits := payloadBits) (restLen := payloadLen)
      hbit hcur
  let codeBits := codeLenTokenStreamBits codeTokens.toList
  let codeLen := codeLenTokenStreamLen codeTokens.toList
  let restAfterPrefixBits := codeBits ||| (payloadBits <<< codeLen)
  let restAfterPrefixLen := codeLen + payloadLen
  let parserBits := Png.generatedDynamicHeaderPrefixBits 286 30 |||
    (restAfterPrefixBits <<< Png.generatedDynamicHeaderPrefixLen)
  let parserLen := Png.generatedDynamicHeaderPrefixLen + restAfterPrefixLen
  have hbitsEq : parserBits = suffixBits := by
    have hshiftPayload :
        (payloadBits <<< codeLen) <<< Png.generatedDynamicHeaderPrefixLen =
          payloadBits <<<
            (Png.generatedDynamicHeaderPrefixLen + codeLen) := by
      calc
        (payloadBits <<< codeLen) <<< Png.generatedDynamicHeaderPrefixLen =
            payloadBits <<<
              (codeLen + Png.generatedDynamicHeaderPrefixLen) := by
              simp [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_assoc,
                Nat.mul_comm, Nat.mul_left_comm]
        _ = payloadBits <<<
              (Png.generatedDynamicHeaderPrefixLen + codeLen) := by
              rw [Nat.add_comm]
    simp [parserBits, restAfterPrefixBits, codeBits, codeLen, suffixBits,
      headerBits, headerLen, prefixBits, Png.generatedDynamicLitLenCount,
      Png.generatedDynamicDistCount, Nat.or_assoc, Nat.shiftLeft_or_distrib,
      hshiftPayload, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hlenEq : parserLen = suffixLen := by
    simp [parserLen, restAfterPrefixLen, codeLen, suffixLen, headerLen,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  simpa [litLenLengths, distLengths, lengths, codeTokens, prefixBits,
    headerBits, headerLen, payloadBits, payloadLen, suffixBits, suffixLen,
    suffixWriter, streamReaderHeader, bwPayloadStart, brPayload,
    codeBits, codeLen, restAfterPrefixBits, restAfterPrefixLen,
    parserBits, parserLen, hbitsEq, hlenEq] using htables

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Decodes the LZ77 payload that follows the generated dynamic header in the
packed suffix. This transports the payload reader produced by header parsing
to the existing generated LZ77 payload decoder theorem. -/
lemma decodeCompressedBlock_deflateTokensLz77Payload_suffix_readerAt_writeBits
    (raw : ByteArray) (hdrHeader : Png.BitWriter)
    (hbit : hdrHeader.bitPos < 8) (hcur : hdrHeader.curClearAbove) :
    let source := Png.deflateTokensLz77 raw
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
    let distCodes := Png.canonicalRevCodesFromLengths distLengths
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    let payloadBits :=
      dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let payloadLen :=
      dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let suffixBits := headerBits ||| (payloadBits <<< headerLen)
    let suffixLen := headerLen + payloadLen
    let suffixWriter :=
      Png.BitWriter.writeBits hdrHeader suffixBits suffixLen
    let bwPayloadStart :=
      Png.BitWriter.writeBits hdrHeader suffixBits headerLen
    let brPayload := Png.BitWriter.readerAt bwPayloadStart
      suffixWriter.flush
      (by
        have hk : headerLen ≤ suffixLen := by omega
        simpa [bwPayloadStart, suffixWriter, suffixLen] using
          Png.flush_size_writeBits_prefix hdrHeader suffixBits
            headerLen suffixLen hk)
      (Png.bitPos_lt_8_writeBits hdrHeader suffixBits headerLen hbit)
    let brFinal := Png.BitWriter.readerAt suffixWriter suffixWriter.flush
      (by rfl)
      (Png.bitPos_lt_8_writeBits hdrHeader suffixBits suffixLen hbit)
    Png.decodeCompressedBlock
      (generatedDynamicTableSpecLz77 source).litLenTable
      (generatedDynamicTableSpecLz77 source).distTable
      brPayload ByteArray.empty = some (brFinal, raw) := by
  intro source litLenLengths distLengths litLenCodes distCodes lengths
    codeTokens prefixBits headerBits headerLen payloadBits payloadLen
    suffixBits suffixLen suffixWriter bwPayloadStart brPayload brFinal
  let bwPayloadAll :=
    Png.BitWriter.writeBits bwPayloadStart payloadBits payloadLen
  have hpayloadAll :
      bwPayloadAll = suffixWriter := by
    simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
      lengths, codeTokens, prefixBits, headerBits, headerLen, payloadBits,
      payloadLen, suffixBits, suffixLen, bwPayloadStart, bwPayloadAll,
      suffixWriter] using
      generatedDynamicPayloadLz77PrefixWriter_eq_suffixWriter source hdrHeader
  have hbitPayload :
      bwPayloadStart.bitPos < 8 :=
    Png.bitPos_lt_8_writeBits hdrHeader suffixBits headerLen hbit
  have hcurPayload :
      bwPayloadStart.curClearAbove :=
    Png.curClearAbove_writeBits hdrHeader suffixBits headerLen hbit hcur
  have hdecode :=
    decodeCompressedBlock_deflateTokensLz77Payload_readerAt_writeBits
      (raw := raw) (bw := bwPayloadStart) hbitPayload hcurPayload
  have hfinalEq :
      Png.BitWriter.readerAt bwPayloadAll bwPayloadAll.flush (by rfl)
        (Png.bitPos_lt_8_writeBits bwPayloadStart payloadBits payloadLen
          hbitPayload) = brFinal := by
    refine readerAt_eq_of_eqs hpayloadAll ?_ _ _ _ _
    exact congrArg Png.BitWriter.flush hpayloadAll
  simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
    payloadBits, payloadLen, bwPayloadStart, bwPayloadAll, brPayload,
    brFinal, hpayloadAll, hfinalEq, generatedDynamicTableSpecLz77] using hdecode

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- The raw dynamic DEFLATE stream produced by the LZ77 encoder is accepted by
the public DEFLATE loop and reconstructs the source bytes. This is the block
loop form used by the zlib-envelope proof. -/
lemma zlibDecompressLoop_deflateDynamicLz77_stream (raw : ByteArray) :
    let source := Png.deflateTokensLz77 raw
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
    let distLengths :=
      Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
    let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
    let distCodes := Png.canonicalRevCodesFromLengths distLengths
    let lengths := generatedDynamicHeaderCodeLengthsLz77 source
    let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
    let prefixBits :=
      Png.generatedDynamicHeaderPrefixBits
        (Png.generatedDynamicLitLenCount litLenLengths)
        (Png.generatedDynamicDistCount distLengths)
    let headerBits :=
      prefixBits |||
        (codeLenTokenStreamBits codeTokens.toList <<<
          Png.generatedDynamicHeaderPrefixLen)
    let headerLen :=
      Png.generatedDynamicHeaderPrefixLen +
        codeLenTokenStreamLen codeTokens.toList
    let payloadBits :=
      dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
    let payloadLen :=
      dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
    let suffixBits := headerBits ||| (payloadBits <<< headerLen)
    let suffixLen := headerLen + payloadLen
    let streamBitsFull := 5 ||| (suffixBits <<< 3)
    let streamLenFull := 3 + suffixLen
    let hdr0 := Png.BitWriter.empty
    let collapsedWriter :=
      Png.BitWriter.writeBits hdr0 streamBitsFull streamLenFull
    let streamReader0 : Png.BitReader := {
      data := collapsedWriter.flush
      bytePos := 0
      bitPos := 0
      hpos := by exact Nat.zero_le _
      hend := by intro _; rfl
      hbit := by decide
    }
    let streamReaderFinal := Png.BitWriter.readerAt collapsedWriter
      collapsedWriter.flush (by rfl)
      (Png.bitPos_lt_8_writeBits hdr0 streamBitsFull streamLenFull
        (by decide))
    Png.zlibDecompressLoop streamReader0 ByteArray.empty =
      some (streamReaderFinal, raw) := by
  intro source litLenLengths distLengths litLenCodes distCodes lengths
    codeTokens prefixBits headerBits headerLen payloadBits payloadLen
    suffixBits suffixLen streamBitsFull streamLenFull hdr0 collapsedWriter
    streamReader0 streamReaderFinal
  let hdrHeader := Png.BitWriter.writeBits hdr0 5 3
  let suffixWriter :=
    Png.BitWriter.writeBits hdrHeader suffixBits suffixLen
  have hbitHeader : hdrHeader.bitPos < 8 := by
    simpa [hdrHeader] using Png.bitPos_lt_8_writeBits hdr0 5 3 (by decide)
  let streamReaderHeader := Png.BitWriter.readerAt hdrHeader
    suffixWriter.flush
    (Png.flush_size_writeBits_le hdrHeader suffixBits suffixLen)
    hbitHeader
  have hcurHeader : hdrHeader.curClearAbove := by
    simpa [hdrHeader] using
      Png.curClearAbove_writeBits hdr0 5 3 (by decide) Png.curClearAbove_empty
  have hstream :
      collapsedWriter = suffixWriter := by
    have h :=
      Png.writeBits_concat hdr0 5 suffixBits 3 suffixLen
        (by decide : 5 < 2 ^ 3)
    simpa [collapsedWriter, suffixWriter, hdrHeader, streamBitsFull,
      streamLenFull] using h
  have hcond :
      streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [streamReader0, Png.BitWriter.readerAt, hdr0,
      Png.BitWriter.empty, collapsedWriter] using
      (Png.readerAt_writeBits_bound (bw := hdr0) (bits := streamBitsFull)
        (len := streamLenFull) (k := 3) (hk := by omega)
        (hbit := by decide))
  have hread3 :
      streamReader0.readBits 3 hcond = (5, streamReaderHeader) := by
    have h :=
      finalDynamicReader0_readBits3 suffixBits suffixLen
    simpa [hdr0, hdrHeader, streamBitsFull, streamLenFull,
      collapsedWriter, streamReader0, streamReaderHeader, suffixWriter]
      using h
  let bwPayloadStart :=
    Png.BitWriter.writeBits hdrHeader suffixBits headerLen
  let brPayload := Png.BitWriter.readerAt bwPayloadStart suffixWriter.flush
    (by
      have hk : headerLen ≤ suffixLen := by omega
      simpa [bwPayloadStart, suffixWriter, suffixLen] using
        Png.flush_size_writeBits_prefix hdrHeader suffixBits headerLen
          suffixLen hk)
    (Png.bitPos_lt_8_writeBits hdrHeader suffixBits headerLen hbitHeader)
  let brSuffixFinal := Png.BitWriter.readerAt suffixWriter suffixWriter.flush
    (by rfl)
    (Png.bitPos_lt_8_writeBits hdrHeader suffixBits suffixLen hbitHeader)
  have htables :
      Png.readDynamicTables streamReaderHeader =
        some ((generatedDynamicTableSpecLz77 source).litLenTable,
          (generatedDynamicTableSpecLz77 source).distTable, brPayload) := by
    simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
      lengths, codeTokens, prefixBits, headerBits, headerLen, payloadBits,
      payloadLen, suffixBits, suffixLen, suffixWriter, streamReaderHeader,
      bwPayloadStart, brPayload] using
      readDynamicTables_generatedDynamicLz77Suffix_readerAt_writeBits
        source hdrHeader hbitHeader hcurHeader
  have hdecode :
      Png.decodeCompressedBlock
        (generatedDynamicTableSpecLz77 source).litLenTable
        (generatedDynamicTableSpecLz77 source).distTable brPayload
        ByteArray.empty = some (brSuffixFinal, raw) := by
    simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
      lengths, codeTokens, prefixBits, headerBits, headerLen, payloadBits,
      payloadLen, suffixBits, suffixLen, suffixWriter, bwPayloadStart,
      brPayload, brSuffixFinal] using
      decodeCompressedBlock_deflateTokensLz77Payload_suffix_readerAt_writeBits
        raw hdrHeader hbitHeader hcurHeader
  change
    Png.zlibDecompressLoopFuel (streamReader0.data.size * 8 + 1)
      streamReader0 ByteArray.empty = some (streamReaderFinal, raw)
  have hloop :=
    zlibDecompressLoopFuel_step_dynamic_final_of_readDynamicTables
      (fuel := streamReader0.data.size * 8)
      (br := streamReader0) (brHeader := streamReaderHeader)
      (brPayload := brPayload) (brFinal := brSuffixFinal)
      (out := ByteArray.empty) (out' := raw)
      (spec := generatedDynamicTableSpecLz77 source)
      hcond hread3 htables hdecode
  have hfinalEq : brSuffixFinal = streamReaderFinal := by
    refine readerAt_eq_of_eqs hstream.symm ?_ _ _ _ _
    exact congrArg Png.BitWriter.flush hstream.symm
  simpa [hfinalEq] using hloop

/-- Public-loop form of the LZ77 dynamic block proof. It hides the generated
writer normalization and records the aligned final byte position needed by the
zlib envelope proof. -/
lemma zlibDecompressLoop_deflateDynamicLz77 (raw : ByteArray) :
    let deflated := Png.deflateDynamicLz77 raw
    let br0 : Png.BitReader := {
      data := deflated
      bytePos := 0
      bitPos := 0
      hpos := by exact Nat.zero_le _
      hend := by intro _; rfl
      hbit := by decide
    }
    ∃ brFinal,
      Png.zlibDecompressLoop br0 ByteArray.empty = some (brFinal, raw) ∧
        brFinal.alignByte.bytePos = deflated.size := by
  intro deflated br0
  let source := Png.deflateTokensLz77 raw
  let litLenLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
  let distCodes := Png.canonicalRevCodesFromLengths distLengths
  let lengths := generatedDynamicHeaderCodeLengthsLz77 source
  let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
  let prefixBits :=
    Png.generatedDynamicHeaderPrefixBits
      (Png.generatedDynamicLitLenCount litLenLengths)
      (Png.generatedDynamicDistCount distLengths)
  let headerBits :=
    prefixBits |||
      (codeLenTokenStreamBits codeTokens.toList <<<
        Png.generatedDynamicHeaderPrefixLen)
  let headerLen :=
    Png.generatedDynamicHeaderPrefixLen +
      codeLenTokenStreamLen codeTokens.toList
  let payloadBits :=
    dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
  let payloadLen :=
    dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
  let suffixBits := headerBits ||| (payloadBits <<< headerLen)
  let suffixLen := headerLen + payloadLen
  let streamBitsFull := 5 ||| (suffixBits <<< 3)
  let streamLenFull := 3 + suffixLen
  let hdr0 := Png.BitWriter.empty
  let collapsedWriter :=
    Png.BitWriter.writeBits hdr0 streamBitsFull streamLenFull
  have hdeflated : deflated = collapsedWriter.flush := by
    simpa [deflated, source, litLenLengths, distLengths, litLenCodes,
      distCodes, lengths, codeTokens, prefixBits, headerBits, headerLen,
      payloadBits, payloadLen, suffixBits, suffixLen, streamBitsFull,
      streamLenFull, hdr0, collapsedWriter] using
      deflateDynamicLz77_eq_collapsedWriter raw
  let brFinal := Png.BitWriter.readerAt collapsedWriter
    collapsedWriter.flush (by rfl)
    (Png.bitPos_lt_8_writeBits hdr0 streamBitsFull streamLenFull
      (by decide))
  refine ⟨brFinal, ?_, ?_⟩
  · simpa [deflated, br0, source, litLenLengths, distLengths, litLenCodes,
      distCodes, lengths, codeTokens, prefixBits, headerBits, headerLen,
      payloadBits, payloadLen, suffixBits, suffixLen, streamBitsFull,
      streamLenFull, hdr0, collapsedWriter, brFinal, hdeflated] using
      zlibDecompressLoop_deflateDynamicLz77_stream raw
  · calc
      brFinal.alignByte.bytePos = collapsedWriter.flush.size := by
        simpa [brFinal] using
          Png.readerAt_alignByte_bytePos_eq_flush
            (bw := collapsedWriter)
            (hbit := Png.bitPos_lt_8_writeBits hdr0 streamBitsFull
              streamLenFull (by decide))
      _ = deflated.size := by
        simp [hdeflated]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Stored-only inflation rejects the public LZ77 dynamic stream because its
first block is dynamic, not stored. This discharges zlib fallback ordering. -/
lemma inflateStored_deflateDynamicLz77_none (raw : ByteArray) :
    Png.inflateStored (Png.deflateDynamicLz77 raw) = none := by
  let source := Png.deflateTokensLz77 raw
  let litLenLengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqsLz77 source)
  let distLengths :=
    Png.generatedDynamicDistLengthsLz77 (Png.distSymbolFreqsLz77 source)
  let litLenCodes := Png.canonicalRevCodesFromLengths litLenLengths
  let distCodes := Png.canonicalRevCodesFromLengths distLengths
  let lengths := generatedDynamicHeaderCodeLengthsLz77 source
  let codeTokens := Png.codeLenLiteralTokensOfLengths lengths
  let prefixBits :=
    Png.generatedDynamicHeaderPrefixBits
      (Png.generatedDynamicLitLenCount litLenLengths)
      (Png.generatedDynamicDistCount distLengths)
  let headerBits :=
    prefixBits |||
      (codeLenTokenStreamBits codeTokens.toList <<<
        Png.generatedDynamicHeaderPrefixLen)
  let headerLen :=
    Png.generatedDynamicHeaderPrefixLen +
      codeLenTokenStreamLen codeTokens.toList
  let payloadBits :=
    dynamicPayloadLz77StreamBits litLenCodes distCodes source.toList
  let payloadLen :=
    dynamicPayloadLz77StreamLen litLenCodes distCodes source.toList
  let suffixBits := headerBits ||| (payloadBits <<< headerLen)
  let suffixLen := headerLen + payloadLen
  let streamBitsFull := 5 ||| (suffixBits <<< 3)
  let streamLenFull := 3 + suffixLen
  let hdr0 := Png.BitWriter.empty
  let collapsedWriter := Png.BitWriter.writeBits hdr0 streamBitsFull streamLenFull
  let streamReader0 : Png.BitReader := {
    data := collapsedWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  have hdata :
      Png.deflateDynamicLz77 raw = collapsedWriter.flush := by
    simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
      lengths, codeTokens, prefixBits, headerBits, headerLen, payloadBits,
      payloadLen, suffixBits, suffixLen, streamBitsFull, streamLenFull,
      hdr0, collapsedWriter] using
      deflateDynamicLz77_eq_collapsedWriter raw
  have hread0 : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [streamReader0, Png.BitWriter.readerAt, hdr0, Png.BitWriter.empty,
      collapsedWriter] using
      (Png.readerAt_writeBits_bound (bw := hdr0) (bits := streamBitsFull)
        (len := streamLenFull) (k := 3) (hk := by omega)
        (hbit := by decide))
  have hread :
      streamReader0.readBits 3 hread0 =
        (5,
          Png.BitWriter.readerAt (Png.BitWriter.writeBits hdr0 5 3)
            (Png.BitWriter.writeBits (Png.BitWriter.writeBits hdr0 5 3)
              suffixBits suffixLen).flush
            (Png.flush_size_writeBits_le (Png.BitWriter.writeBits hdr0 5 3)
              suffixBits suffixLen)
            (by
              simpa using Png.bitPos_lt_8_writeBits hdr0 5 3 (by decide))) := by
    simpa [source, litLenLengths, distLengths, litLenCodes, distCodes,
      lengths, codeTokens, prefixBits, headerBits, headerLen, payloadBits,
      payloadLen, suffixBits, suffixLen, streamBitsFull, streamLenFull,
      hdr0, collapsedWriter, streamReader0] using
      finalDynamicReader0_readBits3 suffixBits suffixLen
  have hreadAux :
      streamReader0.readBits 3 hread0 = streamReader0.readBitsAux 3 := by
    simpa [Png.BitReader.readBits] using
      (Png.readBitsFastU32_eq_readBitsAux (br := streamReader0) (n := 3)
        (h := hread0))
  have hpos : 0 < collapsedWriter.flush.size := by
    have : 3 ≤ collapsedWriter.flush.size * 8 := by
      simpa [streamReader0] using hread0
    by_contra hzero
    have hsize0 : collapsedWriter.flush.size = 0 := Nat.eq_zero_of_not_pos hzero
    omega
  have haux :
      streamReader0.readBitsAux 3 =
        (((collapsedWriter.flush.get 0 hpos).toNat >>> 0) % 2 ^ 3,
          { data := collapsedWriter.flush
            bytePos := 0
            bitPos := 3
            hpos := by exact Nat.zero_le _
            hend := by
              intro hEq
              have : False := by
                simp [hEq] at hpos
              exact False.elim this
            hbit := by decide }) := by
    simpa [streamReader0] using
      (Png.readBitsAux_within_byte_lt (br := streamReader0) (n := 3)
        (hspan := by simp [streamReader0]) (hlt := hpos))
  have hmod :
      ((collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3) = 5 := by
    have hreadFst : (streamReader0.readBits 3 hread0).1 = 5 := by
      simpa using congrArg Prod.fst hread
    have hauxFst :
        (streamReader0.readBitsAux 3).1 =
          ((collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3) := by
      simpa using congrArg Prod.fst haux
    calc
      (collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3 =
          (streamReader0.readBitsAux 3).1 := hauxFst.symm
      _ = (streamReader0.readBits 3 hread0).1 := by
        simp [hreadAux]
      _ = 5 := hreadFst
  have hbit2mod :
      (((collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3).testBit 2) =
        true := by
    rw [hmod]
    decide
  have hbit2 : ((collapsedWriter.flush.get 0 hpos).toNat).testBit 2 = true := by
    have hbit2mod' := hbit2mod
    rw [Nat.testBit_mod_two_pow] at hbit2mod'
    simpa using hbit2mod'
  let header := collapsedWriter.flush.get 0 hpos
  have hmaskedBit : (((header.toNat >>> 1) &&& 3).testBit 1) = true := by
    simp [header, hbit2, Nat.testBit_shiftRight]
    decide
  have hbtypeNat : ((header.toNat >>> 1) &&& 3) ≠ 0 := by
    intro hzero
    have : (((header.toNat >>> 1) &&& 3).testBit 1) = false := by
      simp [hzero]
    rw [hmaskedBit] at this
    cases this
  have hbtype : ((header >>> 1) &&& (0x03 : UInt8)) ≠ 0 := by
    intro h0
    have h0' : (header.toNat >>> 1) &&& 3 = 0 := by
      have h0' := congrArg UInt8.toNat h0
      simpa [UInt8.toNat_and, UInt8.toNat_shiftRight] using h0'
    exact hbtypeNat h0'
  have hauxNone : Png.inflateStoredAux collapsedWriter.flush hpos = none := by
    unfold Png.inflateStoredAux
    simp [header, hbtype]
  have hstored : Png.inflateStored collapsedWriter.flush = none := by
    simp [Png.inflateStored, hpos, hauxNone]
  simpa [hdata] using hstored

end Lemmas

end Bitmaps
