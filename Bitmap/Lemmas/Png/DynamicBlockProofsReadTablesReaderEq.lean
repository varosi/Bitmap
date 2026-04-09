import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesWriteBitsEq

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
lemma dynamicHeaderCodeLenSyms_readerAt_eq
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
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
        (bitPos_lt_8_writeBits bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
          (2 * dynamicHeaderCodeLenSyms.length)
          (by
            have : bw44.bitPos < 8 := by
              simpa [bw44] using bitPos_lt_8_writeBits bw bitsTot 44 hbit
            exact this)) =
      BitWriter.readerAt (BitWriter.writeBits bw bitsTot dynamicHeaderTableLen)
        bw'.flush
        (by
          have hk : dynamicHeaderTableLen ≤ lenTot := by
            simpa [lenTot] using dynamicHeaderTableLen_le_readLen restLen
          simpa [bw', lenTot] using
            (flush_size_writeBits_prefix bw bitsTot dynamicHeaderTableLen lenTot hk))
        (bitPos_lt_8_writeBits bw bitsTot dynamicHeaderTableLen hbit) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw44 := BitWriter.writeBits bw bitsTot 44
  have hbit44 : bw44.bitPos < 8 := by
    simpa [bw44] using bitPos_lt_8_writeBits bw bitsTot 44 hbit
  refine readerAt_eq_of_eqs ?_ rfl _ _ _ _
  simpa [bitsTot, bw44] using dynamicHeaderCodeLenSyms_writeBits_eq (bw := bw) (restBits := restBits)

end Png

end Bitmaps
