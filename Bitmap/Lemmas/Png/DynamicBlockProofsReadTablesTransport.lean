import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesReaderTransport

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
lemma readDynamicTablesAfterHeader_readerAt_writeBits_full
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderReadBits restBits
    let lenTot := dynamicHeaderReadLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let bw14 := BitWriter.writeBits bw bitsTot 14
    let br14 := BitWriter.readerAt bw14 bw'.flush
      (by
        have hk : 14 ≤ lenTot := by
          simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
        simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
      (bitPos_lt_8_writeBits bw bitsTot 14 hbit)
    readDynamicTablesAfterHeader br14 =
      some (fixedLitLenHuffman, fixedDistHuffman, dynamicTablesReaderAt bw restBits restLen hbit) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw14 := BitWriter.writeBits bw bitsTot 14
  let br14 := BitWriter.readerAt bw14 bw'.flush
    (by
      have hk : 14 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
      simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 14 hbit)
  have hbit14 : bw14.bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw bitsTot 14 hbit
  have hcur14 : bw14.curClearAbove := by
    exact curClearAbove_writeBits bw bitsTot 14 hbit hcur
  have hbw14Full :
      bw' = BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits) (dynamicHeaderCodeLenLensLen restLen) := by
    have hk14 : 14 ≤ lenTot := by
      simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
    have hshift14 : bitsTot >>> 14 = dynamicHeaderCodeLenLensBits restBits := by
      simpa [bitsTot] using dynamicHeaderReadBits_shift14 restBits
    have hlen14 : lenTot - 14 = dynamicHeaderCodeLenLensLen restLen := by
      simpa [lenTot] using dynamicHeaderReadLen_sub14 restLen
    calc
      bw' = BitWriter.writeBits bw bitsTot (14 + (lenTot - 14)) := by
        simp [bw', Nat.add_sub_of_le hk14]
      _ = BitWriter.writeBits (BitWriter.writeBits bw bitsTot 14) (bitsTot >>> 14) (lenTot - 14) := by
        simpa using writeBits_split bw bitsTot 14 (lenTot - 14)
      _ = BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits) (dynamicHeaderCodeLenLensLen restLen) := by
        rw [hshift14, hlen14]
  have hfull14Flush :
      (BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits) (dynamicHeaderCodeLenLensLen restLen)).flush =
        bw'.flush := by
    simpa [bw'] using congrArg BitWriter.flush hbw14Full.symm
  have hpost0 :=
    readDynamicTablesAfterHeader_readerAt_writeBits
      (bw := bw14) (restBits := restBits) (restLen := restLen) hbit14 hcur14
  have hpost :
      readDynamicTablesAfterHeader br14 =
        some
          (fixedLitLenHuffman, fixedDistHuffman,
            dynamicTablesAfterHeaderReaderAt bw14 restBits restLen hbit14) := by
    simpa [br14, hfull14Flush] using hpost0
  have hreader :
      dynamicTablesAfterHeaderReaderAt bw14 restBits restLen hbit14 =
        dynamicTablesReaderAt bw restBits restLen hbit := by
    simpa [bitsTot, lenTot, bw', bw14] using
      dynamicTablesAfterHeaderReaderAt_eq_dynamicTablesReaderAt
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit
  simpa [hreader] using hpost

end Png

end Bitmaps
