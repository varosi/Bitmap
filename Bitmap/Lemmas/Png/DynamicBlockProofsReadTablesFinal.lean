import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesPrefix
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesTransport

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
private lemma readDynamicTablesAfterPrefix_readerAt_writeBits
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
      some
        (fixedLitLenHuffman, fixedDistHuffman,
          dynamicTablesReaderAt bw restBits restLen hbit) := by
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
  have hafterHeader :
      readDynamicTablesAfterHeader br14 =
        some (fixedLitLenHuffman, fixedDistHuffman, dynamicTablesReaderAt bw restBits restLen hbit) := by
    simpa [bitsTot, lenTot, bw', bw14, br14] using
      readDynamicTablesAfterHeader_readerAt_writeBits_full
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur
  exact hafterHeader

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
lemma readDynamicTables_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderReadBits restBits
    let lenTot := dynamicHeaderReadLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicTables br =
      some
        (fixedLitLenHuffman, fixedDistHuffman,
          dynamicTablesReaderAt bw restBits restLen hbit) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br5 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 5) bw'.flush
    (by
      have hk : 5 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
      simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 5 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  let br10 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 10) bw'.flush
    (by
      have hk : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
      simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 10 hbit)
  let bw14 := BitWriter.writeBits bw bitsTot 14
  let br14 := BitWriter.readerAt bw14 bw'.flush
    (by
      have hk : 14 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
      simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 14 hbit)
  have hprefix :=
    readDynamicTablesPrefix_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur
  have hreadHlit :
      br.readBits 5
          (by
            have hk : 5 ≤ lenTot := by
              simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
            simpa [br, bw', lenTot] using
              (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5) hk hbit)) =
        (31, br5) := hprefix.1
  have hreadHdist :
      br5.readBits 5
          (by
            have hk : 5 ≤ lenTot - 5 := by
              simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
            simpa [br5, bw', lenTot] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits bw bitsTot 5) (bits := bitsTot >>> 5) (len := lenTot - 5)
                (k := 5) hk (bitPos_lt_8_writeBits bw bitsTot 5 hbit))) =
        (31, br10) := hprefix.2.1
  have hreadHclen :
      br10.readBits 4
          (by
            have hk : 4 ≤ lenTot - 10 := by
              simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
            simpa [br10, bw', lenTot] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits bw bitsTot 10) (bits := bitsTot >>> 10) (len := lenTot - 10)
                (k := 4) hk (bitPos_lt_8_writeBits bw bitsTot 10 hbit))) =
        (6, br14) := hprefix.2.2
  have hafterHeader :
      readDynamicTablesAfterHeader br14 =
        some (fixedLitLenHuffman, fixedDistHuffman, dynamicTablesReaderAt bw restBits restLen hbit) := by
    simpa [bitsTot, lenTot, bw', bw14, br14] using
      readDynamicTablesAfterPrefix_readerAt_writeBits
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur
  unfold readDynamicTables
  rw [hreadHlit, hreadHdist, hreadHclen]
  change readDynamicTablesAfterHeader br14 =
    some (fixedLitLenHuffman, fixedDistHuffman, dynamicTablesReaderAt bw restBits restLen hbit)
  exact hafterHeader

end Png

end Bitmaps
