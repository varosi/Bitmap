import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesPrefix

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Specializes the prefix proof to the concrete first `readBits 5` call in `readDynamicTables`. -/
lemma readDynamicTables_hlit_readerAt_writeBits
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
    br.readBits
        5
        (by
          have hk : 5 ≤ lenTot := by
            simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
          simpa [br, bw', lenTot] using
            (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5) hk hbit)) =
      (31, br5) := by
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
  simpa [bitsTot, lenTot, bw', br, br5] using
    (readDynamicTablesPrefix_hlit_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Specializes the prefix proof to the concrete second `readBits 5` call in `readDynamicTables`. -/
lemma readDynamicTables_hdist_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderReadBits restBits
    let lenTot := dynamicHeaderReadLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
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
    br5.readBits
        5
        (by
          have hk : 5 ≤ lenTot - 5 := by
            simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
          let bw5 := BitWriter.writeBits bw bitsTot 5
          let bwRest5 := BitWriter.writeBits bw5 (bitsTot >>> 5) (lenTot - 5)
          have hflush5 : bwRest5.flush = bw'.flush := by
            calc
              bwRest5.flush =
                  (BitWriter.writeBits
                    (BitWriter.writeBits bw bitsTot 5)
                    (bitsTot >>> 5)
                    (lenTot - 5)).flush := by
                      simp [bw5, bwRest5]
              _ = bw'.flush := by
                  have hsplit :
                      bw' =
                        BitWriter.writeBits
                          (BitWriter.writeBits bw bitsTot 5)
                          (bitsTot >>> 5)
                          (lenTot - 5) := by
                        have hk5 : 5 ≤ lenTot := by
                          simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
                        calc
                          bw' = BitWriter.writeBits bw bitsTot (5 + (lenTot - 5)) := by
                            simp [bw', Nat.add_sub_of_le hk5]
                          _ =
                              BitWriter.writeBits
                                (BitWriter.writeBits bw bitsTot 5)
                                (bitsTot >>> 5)
                                (lenTot - 5) := by
                                  simpa using writeBits_split bw bitsTot 5 (lenTot - 5)
                  simpa [bw'] using congrArg BitWriter.flush hsplit.symm
          have hreader5 :
              BitWriter.readerAt bw5 bwRest5.flush
                  (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
                  (bitPos_lt_8_writeBits bw bitsTot 5 hbit) =
                BitWriter.readerAt bw5 bw'.flush
                  (by
                    have hk5 : 5 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
                    simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 5 lenTot hk5)
                  (bitPos_lt_8_writeBits bw bitsTot 5 hbit) := by
            apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush5)
          have hboundSplit :
              (BitWriter.readerAt bw5 bwRest5.flush
                  (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
                  (bitPos_lt_8_writeBits bw bitsTot 5 hbit)).bitIndex + 5 ≤
                (BitWriter.readerAt bw5 bwRest5.flush
                  (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
                  (bitPos_lt_8_writeBits bw bitsTot 5 hbit)).data.size * 8 := by
            simpa [bw5, bwRest5] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits bw bitsTot 5) (bits := bitsTot >>> 5) (len := lenTot - 5)
                (k := 5) hk (bitPos_lt_8_writeBits bw bitsTot 5 hbit))
          have hboundFull :
              (BitWriter.readerAt bw5 bw'.flush
                  (by
                    have hk5 : 5 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
                    simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 5 lenTot hk5)
                  (bitPos_lt_8_writeBits bw bitsTot 5 hbit)).bitIndex + 5 ≤
                (BitWriter.readerAt bw5 bw'.flush
                  (by
                    have hk5 : 5 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
                    simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 5 lenTot hk5)
                  (bitPos_lt_8_writeBits bw bitsTot 5 hbit)).data.size * 8 := by
            rw [← hreader5]
            exact hboundSplit
          simpa [br5, bw5] using hboundFull) =
      (31, br10) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
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
  simpa [bitsTot, lenTot, bw', br5, br10] using
    (readDynamicTablesPrefix_hdist_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Specializes the prefix proof to the concrete final `readBits 4` call in `readDynamicTables`. -/
lemma readDynamicTables_hclen_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderReadBits restBits
    let lenTot := dynamicHeaderReadLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let bw14 := BitWriter.writeBits bw bitsTot 14
    let br10 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 10) bw'.flush
      (by
        have hk : 10 ≤ lenTot := by
          simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
        simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk)
      (bitPos_lt_8_writeBits bw bitsTot 10 hbit)
    let br14 := BitWriter.readerAt bw14 bw'.flush
      (by
        have hk : 14 ≤ lenTot := by
          simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
        simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
      (bitPos_lt_8_writeBits bw bitsTot 14 hbit)
    br10.readBits
        4
        (by
          have hk : 4 ≤ lenTot - 10 := by
            simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
          let bw10 := BitWriter.writeBits bw bitsTot 10
          let bwRest10 := BitWriter.writeBits bw10 (bitsTot >>> 10) (lenTot - 10)
          have hflush10 : bwRest10.flush = bw'.flush := by
            calc
              bwRest10.flush =
                  (BitWriter.writeBits
                    (BitWriter.writeBits bw bitsTot 10)
                    (bitsTot >>> 10)
                    (lenTot - 10)).flush := by
                      simp [bw10, bwRest10]
              _ = bw'.flush := by
                  have hsplit :
                      bw' =
                        BitWriter.writeBits
                          (BitWriter.writeBits bw bitsTot 10)
                          (bitsTot >>> 10)
                          (lenTot - 10) := by
                        have hk10 : 10 ≤ lenTot := by
                          simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
                        calc
                          bw' = BitWriter.writeBits bw bitsTot (10 + (lenTot - 10)) := by
                            simp [bw', Nat.add_sub_of_le hk10]
                          _ =
                              BitWriter.writeBits
                                (BitWriter.writeBits bw bitsTot 10)
                                (bitsTot >>> 10)
                                (lenTot - 10) := by
                                  simpa using writeBits_split bw bitsTot 10 (lenTot - 10)
                  simpa [bw'] using congrArg BitWriter.flush hsplit.symm
          have hreader10 :
              BitWriter.readerAt bw10 bwRest10.flush
                  (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
                  (bitPos_lt_8_writeBits bw bitsTot 10 hbit) =
                BitWriter.readerAt bw10 bw'.flush
                  (by
                    have hk10 : 10 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
                    simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk10)
                  (bitPos_lt_8_writeBits bw bitsTot 10 hbit) := by
            apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush10)
          have hboundSplit :
              (BitWriter.readerAt bw10 bwRest10.flush
                  (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
                  (bitPos_lt_8_writeBits bw bitsTot 10 hbit)).bitIndex + 4 ≤
                (BitWriter.readerAt bw10 bwRest10.flush
                  (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
                  (bitPos_lt_8_writeBits bw bitsTot 10 hbit)).data.size * 8 := by
            simpa [bw10, bwRest10] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits bw bitsTot 10) (bits := bitsTot >>> 10) (len := lenTot - 10)
                (k := 4) hk (bitPos_lt_8_writeBits bw bitsTot 10 hbit))
          have hboundFull :
              (BitWriter.readerAt bw10 bw'.flush
                  (by
                    have hk10 : 10 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
                    simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk10)
                  (bitPos_lt_8_writeBits bw bitsTot 10 hbit)).bitIndex + 4 ≤
                (BitWriter.readerAt bw10 bw'.flush
                  (by
                    have hk10 : 10 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
                    simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk10)
                  (bitPos_lt_8_writeBits bw bitsTot 10 hbit)).data.size * 8 := by
            rw [← hreader10]
            exact hboundSplit
          simpa [br10, bw10] using hboundFull) =
      (6, br14) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw14 := BitWriter.writeBits bw bitsTot 14
  let br10 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 10) bw'.flush
    (by
      have hk : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
      simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 10 hbit)
  let br14 := BitWriter.readerAt bw14 bw'.flush
    (by
      have hk : 14 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
      simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 14 hbit)
  simpa [bitsTot, lenTot, bw', bw14, br10, br14] using
    (readDynamicTablesPrefix_hclen_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur)

end Png

end Bitmaps
