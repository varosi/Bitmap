import Batteries.Data.UInt
import Bitmap.Lemmas.Png.Lz77
import Bitmap.Lemmas.Png.FixedBlockProofsSpec

namespace Bitmaps

namespace Png

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

end Png

end Bitmaps
