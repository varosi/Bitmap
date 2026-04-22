import Bitmap.Lemmas.Png.FixedBlockProofsCommon

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Writes just the fixed-block end-of-block code, with no trailing payload bits. -/
def eobNoTailWriter (bw : BitWriter) : BitWriter :=
  let sym : Nat := 256
  let codeLen := fixedLitLenCode sym
  let bits := reverseBits codeLen.1 codeLen.2
  BitWriter.writeBits bw bits codeLen.2

/-- Starts a reader at the fixed EOB code so later proofs can replay the terminating decode step. -/
def eobNoTailStartReader (bw : BitWriter) (hbit : bw.bitPos < 8) : BitReader :=
  let bwAll := eobNoTailWriter bw
  BitWriter.readerAt bw bwAll.flush
    (by
      have symEq : (256 : Nat) = 256 := rfl
      simpa [eobNoTailWriter, symEq] using
        (flush_size_writeBits_le (bw := bw)
          (bits := reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (len := (fixedLitLenCode 256).2)))
    hbit

/-- Advances the reader past the fixed EOB code, giving the post-EOB state used by block-end proofs. -/
def eobNoTailAfterReader (bw : BitWriter) (hbit : bw.bitPos < 8) : BitReader :=
  let bwAll := eobNoTailWriter bw
  BitWriter.readerAt bwAll bwAll.flush
    (by rfl)
    (by
      have symEq : (256 : Nat) = 256 := rfl
      simpa [eobNoTailWriter, symEq] using
        (bitPos_lt_8_writeBits (bw := bw)
          (bits := reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (len := (fixedLitLenCode 256).2) hbit))

end Png

end Bitmaps
