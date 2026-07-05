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

end Lemmas

end Bitmaps
