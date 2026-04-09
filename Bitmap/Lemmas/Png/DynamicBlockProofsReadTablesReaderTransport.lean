import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesReaderEq

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
lemma dynamicTablesAfterHeaderReaderAt_eq_dynamicTablesReaderAt
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
    let bitsTot := dynamicHeaderReadBits restBits
    let lenTot := dynamicHeaderReadLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let bw14 := BitWriter.writeBits bw bitsTot 14
    dynamicTablesAfterHeaderReaderAt bw14 restBits restLen
        (bitPos_lt_8_writeBits bw bitsTot 14 hbit) =
      dynamicTablesReaderAt bw restBits restLen hbit := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw14 := BitWriter.writeBits bw bitsTot 14
  let bw44 := BitWriter.writeBits bw bitsTot 44
  have hbit44 : bw44.bitPos < 8 := by
    simpa [bw44] using bitPos_lt_8_writeBits bw bitsTot 44 hbit
  have hafter684 :
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
          (bitPos_lt_8_writeBits bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
            (2 * dynamicHeaderCodeLenSyms.length) hbit44) =
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot dynamicHeaderTableLen)
          bw'.flush
          (by
            have hk : dynamicHeaderTableLen ≤ lenTot := by
              simpa [lenTot] using dynamicHeaderTableLen_le_readLen restLen
            simpa [bw', lenTot] using
              (flush_size_writeBits_prefix bw bitsTot dynamicHeaderTableLen lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot dynamicHeaderTableLen hbit) := by
    simpa [bitsTot, lenTot, bw', bw44] using
      dynamicHeaderCodeLenSyms_readerAt_eq
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit
  simpa [dynamicTablesAfterHeaderReaderAt, dynamicTablesReaderAt, dynamicCodeLenSymsReaderAt,
    bitsTot, lenTot, bw', bw14, bw44]
    using hafter684

end Png

end Bitmaps
