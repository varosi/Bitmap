import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
lemma readDynamicTablesPrefix_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
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
    br.readBits 5
        (by
          have hk : 5 ≤ lenTot := by
            simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
          simpa [br, bw', lenTot] using
            (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5) hk hbit)) =
      (31, br5) ∧
    br5.readBits 5
        (by
          have hk : 5 ≤ lenTot - 5 := by
            simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
          simpa [br5, bw', lenTot] using
            (readerAt_writeBits_bound
              (bw := BitWriter.writeBits bw bitsTot 5) (bits := bitsTot >>> 5) (len := lenTot - 5)
              (k := 5) hk (bitPos_lt_8_writeBits bw bitsTot 5 hbit))) =
      (31, br10) ∧
    br10.readBits 4
        (by
          have hk : 4 ≤ lenTot - 10 := by
            simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
          simpa [br10, bw', lenTot] using
            (readerAt_writeBits_bound
              (bw := BitWriter.writeBits bw bitsTot 10) (bits := bitsTot >>> 10) (len := lenTot - 10)
              (k := 4) hk (bitPos_lt_8_writeBits bw bitsTot 10 hbit))) =
      (6, br14) := by
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
  have hreadHlit :
      br.readBits 5
          (by
            have hk : 5 ≤ lenTot := by
              simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
            simpa [br, bw', lenTot] using
              (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5) hk hbit)) =
        (31, br5) := by
    have hstep :=
      readBits_readerAt_writeBits_shift
        (bw := bw) (bits := bitsTot) (len := lenTot) (skip := 0) (k := 5)
        (by omega)
        (by simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen)
        hbit hcur
    have hmod : (bitsTot >>> 0) % 2 ^ 5 = 31 := by
      simpa [bitsTot] using dynamicHeaderReadBits_low5 restBits
    simpa [br, bw', br5, bitsTot, lenTot, hmod] using hstep
  have hreadHdist :
      br5.readBits 5
          (by
            have hk : 5 ≤ lenTot - 5 := by
              simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
            simpa [br5, bw', lenTot] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits bw bitsTot 5) (bits := bitsTot >>> 5) (len := lenTot - 5)
                (k := 5) hk (bitPos_lt_8_writeBits bw bitsTot 5 hbit))) =
        (31, br10) := by
    have hstep :=
      readBits_readerAt_writeBits_shift
        (bw := bw) (bits := bitsTot) (len := lenTot) (skip := 5) (k := 5)
        (by simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen)
        (by simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen)
        hbit hcur
    have hmod : (bitsTot >>> 5) % 2 ^ 5 = 31 := by
      simpa [bitsTot] using dynamicHeaderReadBits_mid5 restBits
    simpa [br5, bw', br10, bitsTot, lenTot, hmod] using hstep
  have hreadHclen :
      br10.readBits 4
          (by
            have hk : 4 ≤ lenTot - 10 := by
              simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
            simpa [br10, bw', lenTot] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits bw bitsTot 10) (bits := bitsTot >>> 10) (len := lenTot - 10)
                (k := 4) hk (bitPos_lt_8_writeBits bw bitsTot 10 hbit))) =
        (6, br14) := by
    have hstep :=
      readBits_readerAt_writeBits_shift
        (bw := bw) (bits := bitsTot) (len := lenTot) (skip := 10) (k := 4)
        (by simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen)
        (by simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen)
        hbit hcur
    have hmod : (bitsTot >>> 10) % 2 ^ 4 = 6 := by
      simpa [bitsTot] using dynamicHeaderReadBits_high4 restBits
    simpa [br10, bw', br14, bitsTot, lenTot, hmod] using hstep
  exact ⟨hreadHlit, hreadHdist, hreadHclen⟩

end Png

end Bitmaps
