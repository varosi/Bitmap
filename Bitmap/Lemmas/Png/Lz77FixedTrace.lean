import Batteries.Data.UInt
import Bitmap.Lemmas.Png.Lz77
import Bitmap.Lemmas.Png.FixedBlockProofsDecode
import Bitmap.Lemmas.Png.FixedBlockProofsSpec

namespace Bitmaps

namespace Png

/-- Transports `readerAt` across equal writer and backing data values. Match
trace proofs use this when rebracketing proof-facing token bits. -/
lemma lz77ReaderAt_eq_of_eqs
    {bw1 bw2 : BitWriter} {data1 data2 : ByteArray}
    (hbw : bw1 = bw2) (hdata : data1 = data2)
    (hflush1 : bw1.flush.size ≤ data1.size) (hflush2 : bw2.flush.size ≤ data2.size)
    (hbit1 : bw1.bitPos < 8) (hbit2 : bw2.bitPos < 8) :
    BitWriter.readerAt bw1 data1 hflush1 hbit1 =
      BitWriter.readerAt bw2 data2 hflush2 hbit2 := by
  subst hbw
  subst hdata
  apply BitReader.ext <;> simp [BitWriter.readerAt]

/-- Packages the fixed-Huffman EOB bits emitted by the LZ77 fixed payload writer
as a `FixedPayloadFinish`. This is the base case for the future token trace. -/
lemma fixedLz77PayloadFinish_eob_readerAt_writeBits
    (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let eob := fixedLitLenCode 256
    let bits : Nat × Nat := (reverseBits eob.1 eob.2, eob.2)
    let bwAll := BitWriter.writeBits bw bits.1 bits.2
    let br0 := BitWriter.readerAt bw bwAll.flush
      (flush_size_writeBits_le bw bits.1 bits.2) hbit
    let brEnd := BitWriter.readerAt bwAll bwAll.flush (by rfl)
      (bitPos_lt_8_writeBits bw bits.1 bits.2 hbit)
    FixedPayloadFinish br0 out brEnd := by
  intro eob bits bwAll br0 brEnd
  have hsym : (256 : Nat) < 288 := by decide
  have hdecode0 :=
    decodeFixedLiteralSym_readerAt_writeBits' (bw := bw) (sym := 256)
      (restBits := 0) (restLen := 0) hsym hbit hcur
  have hdecode : decodeFixedLiteralSym br0 = some (256, brEnd) := by
    simpa [eob, bits, bwAll, br0, brEnd, Nat.shiftLeft_eq] using hdecode0
  exact FixedPayloadFinish.eob (sym := 256) (br' := brEnd)
    hdecode (by decide) (by decide)

/-- The empty fixed LZ77 payload trace consists only of the fixed-Huffman EOB
symbol. This is the recursive trace builder's base case. -/
lemma fixedLz77PayloadTrace_eob_readerAt_writeBits
    (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let eob := fixedLitLenCode 256
    let bits : Nat × Nat := (reverseBits eob.1 eob.2, eob.2)
    let bwAll := BitWriter.writeBits bw bits.1 bits.2
    let br0 := BitWriter.readerAt bw bwAll.flush
      (flush_size_writeBits_le bw bits.1 bits.2) hbit
    let brEnd := BitWriter.readerAt bwAll bwAll.flush (by rfl)
      (bitPos_lt_8_writeBits bw bits.1 bits.2 hbit)
    FixedPayloadTrace 1 br0 out brEnd out := by
  intro eob bits bwAll br0 brEnd
  have hfinish :=
    fixedLz77PayloadFinish_eob_readerAt_writeBits
      (bw := bw) (out := out) hbit hcur
  exact FixedPayloadTrace.finish (hfinish := by
    simpa [eob, bits, bwAll, br0, brEnd] using hfinish)

/-- A fixed-Huffman literal LZ77 token decodes as one fixed payload literal
transition. Later payload traces use this as the literal step case. -/
lemma fixedLz77PayloadTransition_literal_readerAt_writeBits
    (bw : BitWriter) (out : ByteArray) (b : UInt8) (tail : Nat × Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let head := fixedLz77LiteralBits b
    let bits := lz77BitPairAppend head tail
    let bwAll := BitWriter.writeBits bw bits.1 bits.2
    let br0 := BitWriter.readerAt bw bwAll.flush
      (flush_size_writeBits_le bw bits.1 bits.2) hbit
    let brNext := BitWriter.readerAt (BitWriter.writeBits bw bits.1 head.2) bwAll.flush
      (by
        have hk : head.2 ≤ bits.2 := by
          simp [bits, lz77BitPairAppend]
        exact flush_size_writeBits_prefix bw bits.1 head.2 bits.2 hk)
      (bitPos_lt_8_writeBits bw bits.1 head.2 hbit)
    FixedPayloadTransition br0 out brNext (out.push b) := by
  intro head bits bwAll br0 brNext
  have hsym : b.toNat < 288 := by
    exact lt_trans (UInt8.toNat_lt b) (by decide)
  have hdecode0 :=
    decodeFixedLiteralSym_readerAt_writeBits' (bw := bw) (sym := b.toNat)
      (restBits := tail.1) (restLen := tail.2) hsym hbit hcur
  have hdecode : decodeFixedLiteralSym br0 = some (b.toNat, brNext) := by
    simpa [head, bits, bwAll, br0, brNext, fixedLz77LiteralBits,
      lz77BitPairAppend] using hdecode0
  have hb : u8 b.toNat = b := by
    apply UInt8.ext
    simp [u8]
  have hstep := FixedPayloadTransition.literal (br := br0) (out := out)
    (sym := b.toNat) (br' := brNext) hdecode (by simpa using UInt8.toNat_lt b)
  simpa [hb] using hstep

/-- Prepends one literal-token transition to an existing fixed LZ77 payload
trace. The recursive full-payload trace builder uses this for literal tokens. -/
lemma fixedLz77PayloadTrace_step_literal_readerAt_writeBits
    (bw : BitWriter) (out outFinal : ByteArray) (b : UInt8) (tail : Nat × Nat)
    (steps : Nat) (brAfter : BitReader)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let head := fixedLz77LiteralBits b
    let bits := lz77BitPairAppend head tail
    let bwAll := BitWriter.writeBits bw bits.1 bits.2
    let br0 := BitWriter.readerAt bw bwAll.flush
      (flush_size_writeBits_le bw bits.1 bits.2) hbit
    let brNext := BitWriter.readerAt (BitWriter.writeBits bw bits.1 head.2) bwAll.flush
      (by
        have hk : head.2 ≤ bits.2 := by
          simp [bits, lz77BitPairAppend]
        exact flush_size_writeBits_prefix bw bits.1 head.2 bits.2 hk)
      (bitPos_lt_8_writeBits bw bits.1 head.2 hbit)
    FixedPayloadTrace steps brNext (out.push b) brAfter outFinal →
      FixedPayloadTrace (steps + 1) br0 out brAfter outFinal := by
  intro head bits bwAll br0 brNext hrest
  have hstep :=
    fixedLz77PayloadTransition_literal_readerAt_writeBits
      (bw := bw) (out := out) (b := b) (tail := tail) hbit hcur
  exact FixedPayloadTrace.step (hstep := by
    simpa [head, bits, bwAll, br0, brNext] using hstep) (hrest := hrest)

/-- Builds the declarative fixed-payload copy transition from the four decoder
reads for a length-distance pair. Match bitstream proofs use this wrapper after
showing that their generated bits decode to those reads. -/
lemma fixedPayloadTransition_copy_of_decodes
    (br brLen brDist brCopy brNext : BitReader) (out out' : ByteArray)
    (sym extra len distSym extraD distance : Nat)
    (hsym : 257 ≤ sym ∧ sym ≤ 285)
    (hextra :
      extra =
        Array.getInternal lengthExtra (sym - 257) (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt))
    (hbits : brLen.bitIndex + extra ≤ brLen.data.size * 8)
    (hdist : distSym < distBases.size)
    (hextraD :
      extraD =
        Array.getInternal distExtra distSym (by
          have hDistExtraSize : distExtra.size = 30 := by decide
          have hDistBasesSize : distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist))
    (hbitsD : brCopy.bitIndex + extraD ≤ brCopy.data.size * 8)
    (hdecodeSym : decodeFixedLiteralSym br = some (sym, brLen))
    (hdecodeLen :
      decodeLength sym brLen hsym
        (by
          have hbits' : brLen.bitIndex +
              lengthExtra[sym - 257]'(by
                have hidxle : sym - 257 ≤ 28 := by omega
                have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt) ≤ brLen.data.size * 8 := by
            simpa [hextra] using hbits
          simpa using hbits') = (len, brDist))
    (hdecodeDistSym : decodeFixedDistanceSym brDist = some (distSym, brCopy))
    (hdecodeDist :
      decodeDistance distSym brCopy hdist
        (by
          have hbitsD' : brCopy.bitIndex +
              distExtra[distSym]'(by
                have hDistExtraSize : distExtra.size = 30 := by decide
                have hDistBasesSize : distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist) ≤
              brCopy.data.size * 8 := by
            simpa [hextraD] using hbitsD
          simpa using hbitsD') = (distance, brNext))
    (hcopy : copyDistance out distance len = some out') :
    FixedPayloadTransition br out brNext out' := by
  refine FixedPayloadTransition.copy
    (sym := sym) (extra := extra) (len := len)
    (distSym := distSym) (extraD := extraD) (distance := distance)
    (br' := brLen) (br'' := brDist) (br''' := brCopy)
    (br'''' := brNext) (out' := out')
    hdecodeSym ?_ ?_ hsym hextra hbits hdecodeLen hdecodeDistSym
    hdist hextraD hbitsD hdecodeDist hcopy
  · omega
  · cases hbeq : (sym == 256) with
    | false => simpa using hbeq
    | true =>
        have hs : sym = 256 := by simpa using hbeq
        omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A fixed-Huffman LZ77 match token decodes as one copy transition when the
length and distance metadata are unpacked. This is the match case for the
full fixed-payload LZ77 trace builder. -/
lemma fixedLz77PayloadTransition_match_parts_readerAt_writeBits
    (bw : BitWriter) (out out' : ByteArray)
    (len distance sym extraBits extraLen distSym distExtraBits distExtraLen : Nat)
    (tail : Nat × Nat)
    (hlenInfo : deflateLengthInfo len = (sym, extraBits, extraLen))
    (hdistInfo : deflateDistanceInfo? distance =
      some (distSym, distExtraBits, distExtraLen))
    (hexpand : lz77TokenExpand? out (.match len distance) = some out')
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let symBits : Nat × Nat := (reverseBits codeLen.1 codeLen.2, codeLen.2)
    let lenExtraBits : Nat × Nat := (extraBits, extraLen)
    let distSymBits : Nat × Nat := (reverseBits distSym 5, 5)
    let distExtraPair : Nat × Nat := (distExtraBits, distExtraLen)
    let distExtraTail := lz77BitPairAppend distExtraPair tail
    let distSymTail := lz77BitPairAppend distSymBits distExtraTail
    let lenTail := lz77BitPairAppend lenExtraBits distSymTail
    let bits := lz77BitPairAppend symBits lenTail
    let bwAll := BitWriter.writeBits bw bits.1 bits.2
    let bwSym := BitWriter.writeBits bw bits.1 symBits.2
    let bwLen := BitWriter.writeBits bwSym lenTail.1 lenExtraBits.2
    let bwDistSym := BitWriter.writeBits bwLen distSymTail.1 distSymBits.2
    let bwNext := BitWriter.writeBits bwDistSym distExtraTail.1 distExtraPair.2
    let br0 := BitWriter.readerAt bw bwAll.flush
      (flush_size_writeBits_le bw bits.1 bits.2) hbit
    let brLen := BitWriter.readerAt bwSym bwAll.flush
      (by
        have hk : symBits.2 ≤ bits.2 := by
          simp [bits, lz77BitPairAppend]
        exact flush_size_writeBits_prefix bw bits.1 symBits.2 bits.2 hk)
      (bitPos_lt_8_writeBits bw bits.1 symBits.2 hbit)
    let brDist := BitWriter.readerAt bwLen bwAll.flush
      (by
        have hk1 : lenExtraBits.2 ≤ lenTail.2 := by
          simp [lenTail, lz77BitPairAppend]
        have hflush1 :=
          flush_size_writeBits_prefix bwSym lenTail.1 lenExtraBits.2 lenTail.2 hk1
        have hsymBitsLt : symBits.1 < 2 ^ symBits.2 := by
          simp [symBits, reverseBits_lt]
        have hbwSymOnly :
            bwSym = BitWriter.writeBits bw symBits.1 symBits.2 := by
          dsimp [bwSym, bits]
          exact writeBits_or_shift_tail bw symBits.1 lenTail.1 symBits.2 hsymBitsLt
        have hbwAllLen :
            bwAll = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
          calc
            bwAll =
                BitWriter.writeBits (BitWriter.writeBits bw symBits.1 symBits.2)
                  lenTail.1 lenTail.2 := by
                simpa [bwAll, bits] using
                  (lz77BitPairAppend_writeBits (bw := bw) (head := symBits)
                    (tail := lenTail) hsymBitsLt)
            _ = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
                rw [hbwSymOnly]
        simpa [bwLen, hbwAllLen] using hflush1)
      (bitPos_lt_8_writeBits bwSym lenTail.1 lenExtraBits.2
        (bitPos_lt_8_writeBits bw bits.1 symBits.2 hbit))
    let brCopy := BitWriter.readerAt bwDistSym bwAll.flush
      (by
        have hk2 : distSymBits.2 ≤ distSymTail.2 := by
          simp [distSymTail, lz77BitPairAppend]
        have hflush2 :=
          flush_size_writeBits_prefix bwLen distSymTail.1 distSymBits.2
            distSymTail.2 hk2
        rcases lz77TokenExpand?_match_some_spec (out := out) (out' := out')
            (len := len) (distance := distance) hexpand with
          ⟨hlenLo, hlenHi, _, _, _, _, _⟩
        rcases deflateLengthInfo_decodeLength_correct hlenInfo hlenLo hlenHi with
          ⟨_, _, _, _, _, hbitsLenLt⟩
        have hsymBitsLt : symBits.1 < 2 ^ symBits.2 := by
          simp [symBits, reverseBits_lt]
        have hlenExtraBitsLt : lenExtraBits.1 < 2 ^ lenExtraBits.2 := by
          simpa [lenExtraBits] using hbitsLenLt
        have hbwSymOnly :
            bwSym = BitWriter.writeBits bw symBits.1 symBits.2 := by
          dsimp [bwSym, bits]
          exact writeBits_or_shift_tail bw symBits.1 lenTail.1 symBits.2 hsymBitsLt
        have hbwAllLen :
            bwAll = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
          calc
            bwAll =
                BitWriter.writeBits (BitWriter.writeBits bw symBits.1 symBits.2)
                  lenTail.1 lenTail.2 := by
                simpa [bwAll, bits] using
                  (lz77BitPairAppend_writeBits (bw := bw) (head := symBits)
                    (tail := lenTail) hsymBitsLt)
            _ = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
                rw [hbwSymOnly]
        have hbwLenOnly :
            bwLen = BitWriter.writeBits bwSym lenExtraBits.1 lenExtraBits.2 := by
          dsimp [bwLen, lenTail]
          exact writeBits_or_shift_tail bwSym lenExtraBits.1 distSymTail.1
            lenExtraBits.2 hlenExtraBitsLt
        have hbwAllDist :
            bwAll = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := by
          calc
            bwAll = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := hbwAllLen
            _ =
                BitWriter.writeBits
                  (BitWriter.writeBits bwSym lenExtraBits.1 lenExtraBits.2)
                  distSymTail.1 distSymTail.2 := by
                simpa [lenTail] using
                  (lz77BitPairAppend_writeBits (bw := bwSym) (head := lenExtraBits)
                    (tail := distSymTail) hlenExtraBitsLt)
            _ = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := by
                rw [hbwLenOnly]
        simpa [bwDistSym, hbwAllDist] using hflush2)
      (bitPos_lt_8_writeBits bwLen distSymTail.1 distSymBits.2
        (bitPos_lt_8_writeBits bwSym lenTail.1 lenExtraBits.2
          (bitPos_lt_8_writeBits bw bits.1 symBits.2 hbit)))
    let brNext := BitWriter.readerAt bwNext bwAll.flush
      (by
        have hk3 : distExtraPair.2 ≤ distExtraTail.2 := by
          simp [distExtraTail, lz77BitPairAppend]
        have hflush3 :=
          flush_size_writeBits_prefix bwDistSym distExtraTail.1 distExtraPair.2
            distExtraTail.2 hk3
        rcases lz77TokenExpand?_match_some_spec (out := out) (out' := out')
            (len := len) (distance := distance) hexpand with
          ⟨hlenLo, hlenHi, _, _, _, _, _⟩
        rcases deflateLengthInfo_decodeLength_correct hlenInfo hlenLo hlenHi with
          ⟨_, _, _, _, _, hbitsLenLt⟩
        rcases deflateDistanceInfo_decodeDistance_correct hdistInfo with
          ⟨_, _, _, _, hbitsDistLt⟩
        have hsymBitsLt : symBits.1 < 2 ^ symBits.2 := by
          simp [symBits, reverseBits_lt]
        have hdistSymBitsLt : distSymBits.1 < 2 ^ distSymBits.2 := by
          simpa [distSymBits] using (reverseBits_lt distSym 5)
        have hlenExtraBitsLt : lenExtraBits.1 < 2 ^ lenExtraBits.2 := by
          simpa [lenExtraBits] using hbitsLenLt
        have hbwSymOnly :
            bwSym = BitWriter.writeBits bw symBits.1 symBits.2 := by
          dsimp [bwSym, bits]
          exact writeBits_or_shift_tail bw symBits.1 lenTail.1 symBits.2 hsymBitsLt
        have hbwAllLen :
            bwAll = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
          calc
            bwAll =
                BitWriter.writeBits (BitWriter.writeBits bw symBits.1 symBits.2)
                  lenTail.1 lenTail.2 := by
                simpa [bwAll, bits] using
                  (lz77BitPairAppend_writeBits (bw := bw) (head := symBits)
                    (tail := lenTail) hsymBitsLt)
            _ = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
                rw [hbwSymOnly]
        have hbwLenOnly :
            bwLen = BitWriter.writeBits bwSym lenExtraBits.1 lenExtraBits.2 := by
          dsimp [bwLen, lenTail]
          exact writeBits_or_shift_tail bwSym lenExtraBits.1 distSymTail.1
            lenExtraBits.2 hlenExtraBitsLt
        have hbwAllDist :
            bwAll = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := by
          calc
            bwAll = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := hbwAllLen
            _ =
                BitWriter.writeBits
                  (BitWriter.writeBits bwSym lenExtraBits.1 lenExtraBits.2)
                  distSymTail.1 distSymTail.2 := by
                simpa [lenTail] using
                  (lz77BitPairAppend_writeBits (bw := bwSym) (head := lenExtraBits)
                    (tail := distSymTail) hlenExtraBitsLt)
            _ = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := by
                rw [hbwLenOnly]
        have hbwDistSymOnly :
            bwDistSym = BitWriter.writeBits bwLen distSymBits.1 distSymBits.2 := by
          dsimp [bwDistSym, distSymTail]
          exact writeBits_or_shift_tail bwLen distSymBits.1 distExtraTail.1
            distSymBits.2 hdistSymBitsLt
        have hbwAllDistExtra :
            bwAll = BitWriter.writeBits bwDistSym distExtraTail.1 distExtraTail.2 := by
          calc
            bwAll = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := hbwAllDist
            _ =
                BitWriter.writeBits
                  (BitWriter.writeBits bwLen distSymBits.1 distSymBits.2)
                  distExtraTail.1 distExtraTail.2 := by
                simpa [distSymTail] using
                  (lz77BitPairAppend_writeBits (bw := bwLen) (head := distSymBits)
                    (tail := distExtraTail) hdistSymBitsLt)
            _ = BitWriter.writeBits bwDistSym distExtraTail.1 distExtraTail.2 := by
                rw [hbwDistSymOnly]
        simpa [bwNext, hbwAllDistExtra] using hflush3)
      (bitPos_lt_8_writeBits bwDistSym distExtraTail.1 distExtraPair.2
        (bitPos_lt_8_writeBits bwLen distSymTail.1 distSymBits.2
          (bitPos_lt_8_writeBits bwSym lenTail.1 lenExtraBits.2
            (bitPos_lt_8_writeBits bw bits.1 symBits.2 hbit))))
    FixedPayloadTransition br0 out brNext out' := by
  intro codeLen symBits lenExtraBits distSymBits distExtraPair
    distExtraTail distSymTail lenTail bits bwAll bwSym bwLen bwDistSym
    bwNext br0 brLen brDist brCopy brNext
  rcases lz77TokenExpand?_match_some_spec (out := out) (out' := out')
      (len := len) (distance := distance) hexpand with
    ⟨hlenLo, hlenHi, _hdistLo, _hdistHi, _hdistOut, _hdistSome, _hcopyFast⟩
  rcases deflateLengthInfo_decodeLength_correct hlenInfo hlenLo hlenHi with
    ⟨hsym, hidxBase, hidxExtra, hextraLen, hbaseLen, hbitsLenLt⟩
  rcases deflateDistanceInfo_decodeDistance_correct hdistInfo with
    ⟨hdist, hdistExtra, hextraDist, hbaseDist, hbitsDistLt⟩
  have hsymLt : sym < 288 := by omega
  have hdistSymLt32 : distSym < 32 := by
    have hDistBasesSize : distBases.size = 30 := by decide
    omega
  have hsymBitsLt : symBits.1 < 2 ^ symBits.2 := by
    simp [symBits, reverseBits_lt]
  have hdistSymBitsLt : distSymBits.1 < 2 ^ distSymBits.2 := by
    simpa [distSymBits] using (reverseBits_lt distSym 5)
  have hdistExtraBitsLt : distExtraPair.1 < 2 ^ distExtraPair.2 := by
    simpa [distExtraPair] using hbitsDistLt
  have hlenExtraBitsLt : lenExtraBits.1 < 2 ^ lenExtraBits.2 := by
    simpa [lenExtraBits] using hbitsLenLt
  have hbwSymOnly :
      bwSym = BitWriter.writeBits bw symBits.1 symBits.2 := by
    dsimp [bwSym, bits]
    exact writeBits_or_shift_tail bw symBits.1 lenTail.1 symBits.2 hsymBitsLt
  have hbwAllLen :
      bwAll = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
    calc
      bwAll =
          BitWriter.writeBits (BitWriter.writeBits bw symBits.1 symBits.2)
            lenTail.1 lenTail.2 := by
          simpa [bwAll, bits] using
            (lz77BitPairAppend_writeBits (bw := bw) (head := symBits)
              (tail := lenTail) hsymBitsLt)
      _ = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := by
          rw [hbwSymOnly]
  have hbwLenOnly :
      bwLen = BitWriter.writeBits bwSym lenExtraBits.1 lenExtraBits.2 := by
    dsimp [bwLen, lenTail]
    exact writeBits_or_shift_tail bwSym lenExtraBits.1 distSymTail.1
      lenExtraBits.2 hlenExtraBitsLt
  have hbwAllDist :
      bwAll = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := by
    calc
      bwAll = BitWriter.writeBits bwSym lenTail.1 lenTail.2 := hbwAllLen
      _ =
          BitWriter.writeBits
            (BitWriter.writeBits bwSym lenExtraBits.1 lenExtraBits.2)
            distSymTail.1 distSymTail.2 := by
          simpa [lenTail] using
            (lz77BitPairAppend_writeBits (bw := bwSym) (head := lenExtraBits)
              (tail := distSymTail) hlenExtraBitsLt)
      _ = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := by
          rw [hbwLenOnly]
  have hbwDistSymOnly :
      bwDistSym = BitWriter.writeBits bwLen distSymBits.1 distSymBits.2 := by
    dsimp [bwDistSym, distSymTail]
    exact writeBits_or_shift_tail bwLen distSymBits.1 distExtraTail.1
      distSymBits.2 hdistSymBitsLt
  have hbwAllDistExtra :
      bwAll = BitWriter.writeBits bwDistSym distExtraTail.1 distExtraTail.2 := by
    calc
      bwAll = BitWriter.writeBits bwLen distSymTail.1 distSymTail.2 := hbwAllDist
      _ =
          BitWriter.writeBits
            (BitWriter.writeBits bwLen distSymBits.1 distSymBits.2)
            distExtraTail.1 distExtraTail.2 := by
          simpa [distSymTail] using
            (lz77BitPairAppend_writeBits (bw := bwLen) (head := distSymBits)
              (tail := distExtraTail) hdistSymBitsLt)
      _ = BitWriter.writeBits bwDistSym distExtraTail.1 distExtraTail.2 := by
          rw [hbwDistSymOnly]
  have hbwNextOnly :
      bwNext = BitWriter.writeBits bwDistSym distExtraPair.1 distExtraPair.2 := by
    dsimp [bwNext, distExtraTail]
    exact writeBits_or_shift_tail bwDistSym distExtraPair.1 tail.1
      distExtraPair.2 hdistExtraBitsLt
  have hdecodeSym :
      decodeFixedLiteralSym br0 = some (sym, brLen) := by
    have hdecode0 :=
      decodeFixedLiteralSym_readerAt_writeBits' (bw := bw) (sym := sym)
        (restBits := lenTail.1) (restLen := lenTail.2) hsymLt hbit hcur
    simpa [codeLen, symBits, bits, bwAll, bwSym, br0, brLen]
      using hdecode0
  have hbitLen : bwSym.bitPos < 8 := by
    simpa [bwSym] using bitPos_lt_8_writeBits bw bits.1 symBits.2 hbit
  have hcurLen : bwSym.curClearAbove := by
    simpa [bwSym] using curClearAbove_writeBits bw bits.1 symBits.2 hbit hcur
  have hdecodeLen :
      decodeLength sym brLen hsym
        (by
          have hread :=
            readerAt_writeBits_bound (bw := bwSym) (bits := lenTail.1)
              (len := lenTail.2) (k := extraLen)
              (hk := by simp [lenTail, lenExtraBits, lz77BitPairAppend]) hbitLen
          have hcanon :
              lengthExtra[sym - 257]'(by
                have hidxle : sym - 257 ≤ 28 := by omega
                have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt) = extraLen := by
            calc
              lengthExtra[sym - 257]'(by
                have hidxle : sym - 257 ≤ 28 := by omega
                have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt) =
                  Array.getInternal lengthExtra (sym - 257)
                    (by
                      have hidxle : sym - 257 ≤ 28 := by omega
                      have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                      have hsize : lengthExtra.size = 29 := by decide
                      simpa [hsize] using hidxlt) := rfl
              _ = Array.getInternal lengthExtra (sym - 257) hidxExtra := by
                    congr
              _ = extraLen := by simpa using hextraLen.symm
          simpa [brLen, hbwAllLen, hcanon] using hread) =
        (len, brDist) := by
    have hdecode0 :=
      decodeLength_readerAt_writeBits_prefix (bw := bwSym) (sym := sym)
        (extraBits := extraBits) (extraLen := extraLen)
        (restBits := distSymTail.1) (restLen := distSymTail.2)
        (lenOut := len) (hsym := hsym) (hidxBase := hidxBase)
        (hidxExtra := hidxExtra) (hextra := hextraLen)
        (hbase := hbaseLen) (hbitsLt := hbitsLenLt)
        (hbit := hbitLen) (hcur := hcurLen)
    simpa [lenExtraBits, lenTail, bwLen, brLen, brDist, hbwAllLen]
      using hdecode0
  have hbitDistSym : bwLen.bitPos < 8 := by
    simpa [bwLen] using bitPos_lt_8_writeBits bwSym lenTail.1
      lenExtraBits.2 hbitLen
  have hcurDistSym : bwLen.curClearAbove := by
    simpa [bwLen] using curClearAbove_writeBits bwSym lenTail.1
      lenExtraBits.2 hbitLen hcurLen
  have hdecodeDistSym :
      decodeFixedDistanceSym brDist = some (distSym, brCopy) := by
    have hdecode0 :=
      decodeFixedDistanceSym_readerAt_writeBits_symbol (bw := bwLen)
        (distSym := distSym) (restBits := distExtraTail.1)
        (restLen := distExtraTail.2) hdistSymLt32 hbitDistSym hcurDistSym
    simpa [distSymBits, distSymTail, bwDistSym, brDist, brCopy, hbwAllDist]
      using hdecode0
  have hbitDist : bwDistSym.bitPos < 8 := by
    simpa [bwDistSym] using bitPos_lt_8_writeBits bwLen distSymTail.1
      distSymBits.2 hbitDistSym
  have hcurDist : bwDistSym.curClearAbove := by
    simpa [bwDistSym] using curClearAbove_writeBits bwLen distSymTail.1
      distSymBits.2 hbitDistSym hcurDistSym
  have hdecodeDist :
      decodeDistance distSym brCopy hdist
        (by
          have hread :=
            readerAt_writeBits_bound (bw := bwDistSym) (bits := distExtraTail.1)
              (len := distExtraTail.2) (k := distExtraLen)
              (hk := by simp [distExtraTail, distExtraPair, lz77BitPairAppend]) hbitDist
          have hcanon :
              distExtra[distSym]'(by
                have hDistExtraSize : distExtra.size = 30 := by decide
                have hDistBasesSize : distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist) = distExtraLen := by
            calc
              distExtra[distSym]'(by
                have hDistExtraSize : distExtra.size = 30 := by decide
                have hDistBasesSize : distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist) =
                  Array.getInternal distExtra distSym
                    (by
                      have hDistExtraSize : distExtra.size = 30 := by decide
                      have hDistBasesSize : distBases.size = 30 := by decide
                      simpa [hDistExtraSize, hDistBasesSize] using hdist) := rfl
              _ = Array.getInternal distExtra distSym hdistExtra := by
                    congr
              _ = distExtraLen := by simpa using hextraDist.symm
          simpa [brCopy, hbwAllDistExtra, hcanon] using hread) =
        (distance, brNext) := by
    have hdecode0 :=
      decodeDistance_readerAt_writeBits_prefix (bw := bwDistSym)
        (sym := distSym) (extraBits := distExtraBits)
        (extraLen := distExtraLen) (restBits := tail.1) (restLen := tail.2)
        (distance := distance) (hdist := hdist) (hdistExtra := hdistExtra)
        (hextra := hextraDist) (hbase := hbaseDist) (hbitsLt := hbitsDistLt)
        (hbit := hbitDist) (hcur := hcurDist)
    have hbwNextPrefix :
        BitWriter.writeBits bwDistSym
            (distExtraBits ||| (tail.1 <<< distExtraLen)) distExtraLen =
          BitWriter.writeBits bwDistSym distExtraBits distExtraLen := by
      simpa [bwNext, distExtraPair, distExtraTail, lz77BitPairAppend]
        using hbwNextOnly
    simpa [distExtraPair, distExtraTail, lz77BitPairAppend, bwNext,
      brCopy, brNext, hbwAllDistExtra, hbwNextOnly, hbwNextPrefix] using hdecode0
  have hcopy : copyDistance out distance len = some out' :=
    lz77TokenExpand?_match_some_copyDistance hexpand
  exact fixedPayloadTransition_copy_of_decodes
    (br := br0) (brLen := brLen) (brDist := brDist)
    (brCopy := brCopy) (brNext := brNext) (out := out) (out' := out')
    (sym := sym) (extra := extraLen) (len := len)
    (distSym := distSym) (extraD := distExtraLen) (distance := distance)
    hsym hextraLen (by
      simpa [brLen, hbwAllLen] using
        (readerAt_writeBits_bound (bw := bwSym) (bits := lenTail.1)
          (len := lenTail.2) (k := extraLen)
          (hk := by simp [lenTail, lenExtraBits, lz77BitPairAppend]) hbitLen))
    hdist hextraDist (by
      simpa [brCopy, hbwAllDistExtra] using
        (readerAt_writeBits_bound (bw := bwDistSym) (bits := distExtraTail.1)
          (len := distExtraTail.2) (k := distExtraLen)
          (hk := by simp [distExtraTail, distExtraPair, lz77BitPairAppend]) hbitDist))
    hdecodeSym hdecodeLen hdecodeDistSym hdecodeDist hcopy

end Png

end Bitmaps
