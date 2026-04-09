import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
lemma readDynamicTables_readerAt_writeBits_concrete
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderReadBits restBits
    let lenTot := dynamicHeaderReadLen restLen
    let bwFull := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bwFull.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicTables br =
      some
        (fixedLitLenHuffman, fixedDistHuffman,
          dynamicTablesAfterHeaderReaderAt
            (BitWriter.writeBits bw bitsTot 14) restBits restLen
            (bitPos_lt_8_writeBits bw bitsTot 14 hbit)) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bwFull := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bwFull.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br5 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 5) bwFull.flush
    (by
      have hk : 5 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
      simpa [bwFull, lenTot] using flush_size_writeBits_prefix bw bitsTot 5 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  let br10 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 10) bwFull.flush
    (by
      have hk : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
      simpa [bwFull, lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 10 hbit)
  let bw14 := BitWriter.writeBits bw bitsTot 14
  let br14 := BitWriter.readerAt bw14 bwFull.flush
    (by
      have hk : 14 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
      simpa [bwFull, lenTot] using flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 14 hbit)
  have hreadHlit :
      br.readBits 5
          (by
            have hk : 5 ≤ lenTot := by
              simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
            simpa [br, bwFull, lenTot] using
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
    have hstep' :
        br.readBits 5
            (by
              have hk : 5 ≤ lenTot := by
                simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
              simpa [br, bwFull, lenTot] using
                (readerAt_writeBits_bound
                  (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5) hk hbit)) =
          ((bitsTot >>> 0) % 2 ^ 5, br5) := by
      simpa [br, bwFull, br5, bitsTot, lenTot] using hstep
    rw [hmod] at hstep'
    exact hstep'
  have hreadHdist :
      br5.readBits 5
          (by
            have hk : 5 ≤ lenTot - 5 := by
              simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
            have hbw5Full :
                bwFull =
                  BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5) (lenTot - 5) := by
              have hk5 : 5 ≤ lenTot := by
                simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
              calc
                bwFull = BitWriter.writeBits bw bitsTot (5 + (lenTot - 5)) := by
                  simp [bwFull, Nat.add_sub_of_le hk5]
                _ =
                    BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5)
                      (lenTot - 5) := by
                    simpa using writeBits_split bw bitsTot 5 (lenTot - 5)
            have hflush5 :
                (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5)
                  (lenTot - 5)).flush = bwFull.flush := by
              simpa [bwFull] using congrArg BitWriter.flush hbw5Full.symm
            simpa [br5, hflush5, lenTot] using
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
    have hbw5Full :
        bwFull =
          BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5) (lenTot - 5) := by
      have hk5 : 5 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
      calc
        bwFull = BitWriter.writeBits bw bitsTot (5 + (lenTot - 5)) := by
          simp [bwFull, Nat.add_sub_of_le hk5]
        _ =
            BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5) (lenTot - 5) := by
            simpa using writeBits_split bw bitsTot 5 (lenTot - 5)
    have hflush5 :
        (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5)
          (lenTot - 5)).flush = bwFull.flush := by
      simpa [bwFull] using congrArg BitWriter.flush hbw5Full.symm
    have hstep' :
        br5.readBits 5
            (by
              have hk : 5 ≤ lenTot - 5 := by
                simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
              simpa [br5, hflush5, lenTot] using
                (readerAt_writeBits_bound
                  (bw := BitWriter.writeBits bw bitsTot 5) (bits := bitsTot >>> 5) (len := lenTot - 5)
                  (k := 5) hk (bitPos_lt_8_writeBits bw bitsTot 5 hbit))) =
          ((bitsTot >>> 5) % 2 ^ 5, br10) := by
      simpa [br5, br10, hflush5, bitsTot, lenTot] using hstep
    rw [hmod] at hstep'
    exact hstep'
  have hreadHclen :
      br10.readBits 4
          (by
            have hk : 4 ≤ lenTot - 10 := by
              simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
            have hbw10Full :
                bwFull =
                  BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10) (lenTot - 10) := by
              have hk10 : 10 ≤ lenTot := by
                simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
              calc
                bwFull = BitWriter.writeBits bw bitsTot (10 + (lenTot - 10)) := by
                  simp [bwFull, Nat.add_sub_of_le hk10]
                _ =
                    BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10)
                      (lenTot - 10) := by
                    simpa using writeBits_split bw bitsTot 10 (lenTot - 10)
            have hflush10 :
                (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10)
                  (lenTot - 10)).flush = bwFull.flush := by
              simpa [bwFull] using congrArg BitWriter.flush hbw10Full.symm
            simpa [br10, hflush10, lenTot] using
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
    have hbw10Full :
        bwFull =
          BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10) (lenTot - 10) := by
      have hk10 : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
      calc
        bwFull = BitWriter.writeBits bw bitsTot (10 + (lenTot - 10)) := by
          simp [bwFull, Nat.add_sub_of_le hk10]
        _ =
            BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10) (lenTot - 10) := by
            simpa using writeBits_split bw bitsTot 10 (lenTot - 10)
    have hflush10 :
        (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10)
          (lenTot - 10)).flush = bwFull.flush := by
      simpa [bwFull] using congrArg BitWriter.flush hbw10Full.symm
    have hstep' :
        br10.readBits 4
            (by
              have hk : 4 ≤ lenTot - 10 := by
                simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
              simpa [br10, hflush10, lenTot] using
                (readerAt_writeBits_bound
                  (bw := BitWriter.writeBits bw bitsTot 10) (bits := bitsTot >>> 10) (len := lenTot - 10)
                  (k := 4) hk (bitPos_lt_8_writeBits bw bitsTot 10 hbit))) =
          ((bitsTot >>> 10) % 2 ^ 4, br14) := by
      simpa [br10, br14, hflush10, bitsTot, lenTot] using hstep
    rw [hmod] at hstep'
    exact hstep'
  have hbit14 : bw14.bitPos < 8 := by
    simpa [bw14] using bitPos_lt_8_writeBits bw bitsTot 14 hbit
  have hcur14 : bw14.curClearAbove := by
    simpa [bw14] using curClearAbove_writeBits bw bitsTot 14 hbit hcur
  have hbw14Full :
      bwFull = BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits)
        (dynamicHeaderCodeLenLensLen restLen) := by
    have hk14 : 14 ≤ lenTot := by
      simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
    have hshift14 : bitsTot >>> 14 = dynamicHeaderCodeLenLensBits restBits := by
      simpa [bitsTot] using dynamicHeaderReadBits_shift14 restBits
    have hlen14 : lenTot - 14 = dynamicHeaderCodeLenLensLen restLen := by
      simpa [lenTot] using dynamicHeaderReadLen_sub14 restLen
    calc
      bwFull = BitWriter.writeBits bw bitsTot (14 + (lenTot - 14)) := by
        simp [bwFull, Nat.add_sub_of_le hk14]
      _ = BitWriter.writeBits (BitWriter.writeBits bw bitsTot 14) (bitsTot >>> 14) (lenTot - 14) := by
        simpa using writeBits_split bw bitsTot 14 (lenTot - 14)
      _ = BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits)
            (dynamicHeaderCodeLenLensLen restLen) := by
        rw [hshift14, hlen14]
  have hfull14Flush :
      (BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits)
        (dynamicHeaderCodeLenLensLen restLen)).flush = bwFull.flush := by
    simpa [bwFull] using congrArg BitWriter.flush hbw14Full.symm
  have hafterHeader0 :=
    readDynamicTablesAfterHeader_readerAt_writeBits
      (bw := bw14) (restBits := restBits) (restLen := restLen) hbit14 hcur14
  have hafterHeader :
      readDynamicTablesAfterHeader br14 =
        some
          (fixedLitLenHuffman, fixedDistHuffman,
            dynamicTablesAfterHeaderReaderAt bw14 restBits restLen hbit14) := by
    simpa [br14, hfull14Flush] using hafterHeader0
  have hboundHlit : br.bitIndex + 5 ≤ br.data.size * 8 := by
    have hk : 5 ≤ lenTot := by
      simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
    simpa [br, bwFull, lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5) hk hbit)
  have hboundHdist : br5.bitIndex + 5 ≤ br5.data.size * 8 := by
    have hk : 5 ≤ lenTot - 5 := by
      simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
    have hbw5Full :
        bwFull =
          BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5) (lenTot - 5) := by
      have hk5 : 5 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
      calc
        bwFull = BitWriter.writeBits bw bitsTot (5 + (lenTot - 5)) := by
          simp [bwFull, Nat.add_sub_of_le hk5]
        _ =
            BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5) (lenTot - 5) := by
            simpa using writeBits_split bw bitsTot 5 (lenTot - 5)
    have hflush5 :
        (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 5) (bitsTot >>> 5)
          (lenTot - 5)).flush = bwFull.flush := by
      simpa [bwFull] using congrArg BitWriter.flush hbw5Full.symm
    simpa [br5, hflush5, lenTot] using
      (readerAt_writeBits_bound
        (bw := BitWriter.writeBits bw bitsTot 5) (bits := bitsTot >>> 5) (len := lenTot - 5)
        (k := 5) hk (bitPos_lt_8_writeBits bw bitsTot 5 hbit))
  have hboundHclen : br10.bitIndex + 4 ≤ br10.data.size * 8 := by
    have hk : 4 ≤ lenTot - 10 := by
      simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
    have hbw10Full :
        bwFull =
          BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10) (lenTot - 10) := by
      have hk10 : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
      calc
        bwFull = BitWriter.writeBits bw bitsTot (10 + (lenTot - 10)) := by
          simp [bwFull, Nat.add_sub_of_le hk10]
        _ =
            BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10) (lenTot - 10) := by
            simpa using writeBits_split bw bitsTot 10 (lenTot - 10)
    have hflush10 :
        (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 10) (bitsTot >>> 10)
          (lenTot - 10)).flush = bwFull.flush := by
      simpa [bwFull] using congrArg BitWriter.flush hbw10Full.symm
    simpa [br10, hflush10, lenTot] using
      (readerAt_writeBits_bound
        (bw := BitWriter.writeBits bw bitsTot 10) (bits := bitsTot >>> 10) (len := lenTot - 10)
        (k := 4) hk (bitPos_lt_8_writeBits bw bitsTot 10 hbit))
  have hmain :
      readDynamicTables br =
        some
          (fixedLitLenHuffman, fixedDistHuffman,
            dynamicTablesAfterHeaderReaderAt bw14 restBits restLen hbit14) := by
    unfold readDynamicTables
    simp [hboundHlit, hreadHlit, hboundHdist, hreadHdist, hboundHclen, hreadHclen]
    simpa [readDynamicTablesAfterHeader, readDynamicCodeLenLengths10,
      readDynamicCodeLenLengthsHead5, readDynamicCodeLenLengthsTail5] using hafterHeader
  simpa [bw14, br, bwFull, bitsTot, lenTot] using hmain

end Png

end Bitmaps
