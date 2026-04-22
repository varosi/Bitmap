import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesWriteBitsEq

namespace Bitmaps

namespace Png

def dynamicHeaderCodeLenSymsReaderLocal
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw44 := BitWriter.writeBits bw bitsTot 44
  BitWriter.readerAt
    (BitWriter.writeBits bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
      (2 * dynamicHeaderCodeLenSyms.length))
    bw'.flush
    (by
      have hk : 2 * dynamicHeaderCodeLenSyms.length ≤ dynamicHeaderCodeLenSymsRestLen restLen := by
        simpa using dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms restLen
      simpa using
        (flush_size_writeBits_prefix bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
          (2 * dynamicHeaderCodeLenSyms.length) (dynamicHeaderCodeLenSymsRestLen restLen) hk))
    (by
      have hbit44 : bw44.bitPos < 8 := by
        simpa [bw44] using bitPos_lt_8_writeBits bw bitsTot 44 hbit
      exact bitPos_lt_8_writeBits bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) hbit44)

def dynamicHeaderTableReaderLocal
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  BitWriter.readerAt (BitWriter.writeBits bw bitsTot dynamicHeaderTableLen)
    bw'.flush
    (by
      have hk : dynamicHeaderTableLen ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderTableLen_le_readLen restLen
      simpa [bw', lenTot] using
        (flush_size_writeBits_prefix bw bitsTot dynamicHeaderTableLen lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot dynamicHeaderTableLen hbit)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Matches the direct reader after the code-length symbol block with the staged reader construction. -/
lemma dynamicHeaderCodeLenSyms_readerAt_eq
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
    dynamicHeaderCodeLenSymsReaderLocal bw restBits restLen hbit =
      dynamicHeaderTableReaderLocal bw restBits restLen hbit := by
  let bitsTot := dynamicHeaderReadBits restBits
  let bw44 := BitWriter.writeBits bw bitsTot 44
  have hwriter :
      BitWriter.writeBits bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) =
        BitWriter.writeBits bw bitsTot dynamicHeaderTableLen := by
    simpa [bitsTot, bw44] using
      dynamicHeaderCodeLenSyms_writeBits_eq (bw := bw) (restBits := restBits)
  change dynamicHeaderCodeLenSymsReaderLocal bw restBits restLen hbit =
      dynamicHeaderTableReaderLocal bw restBits restLen hbit
  apply BitReader.ext <;>
    simp [dynamicHeaderCodeLenSymsReaderLocal, dynamicHeaderTableReaderLocal, BitWriter.readerAt, hwriter]

end Png

end Bitmaps
