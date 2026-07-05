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

end Lemmas

end Bitmaps
