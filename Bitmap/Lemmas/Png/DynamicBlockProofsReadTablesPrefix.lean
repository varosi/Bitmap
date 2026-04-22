import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

private def readTablesPrefixBits (restBits : Nat) : Nat :=
  dynamicHeaderReadBits restBits

private def readTablesPrefixLen (restLen : Nat) : Nat :=
  dynamicHeaderReadLen restLen

private def readTablesPrefixWriter (bw : BitWriter) (restBits restLen : Nat) : BitWriter :=
  BitWriter.writeBits bw (readTablesPrefixBits restBits) (readTablesPrefixLen restLen)

private def readTablesPrefixReader
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt bw (readTablesPrefixWriter bw restBits restLen).flush
    (flush_size_writeBits_le bw (readTablesPrefixBits restBits) (readTablesPrefixLen restLen))
    hbit

private def readTablesPrefixReader5
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt (BitWriter.writeBits bw (readTablesPrefixBits restBits) 5)
    (readTablesPrefixWriter bw restBits restLen).flush
    (by
      have hk : 5 ≤ readTablesPrefixLen restLen := by
        simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_5 restLen
      simpa [readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen] using
        (flush_size_writeBits_prefix bw (readTablesPrefixBits restBits) 5
          (readTablesPrefixLen restLen) hk))
    (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 5 hbit)

private def readTablesPrefixReader10
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt (BitWriter.writeBits bw (readTablesPrefixBits restBits) 10)
    (readTablesPrefixWriter bw restBits restLen).flush
    (by
      have hk : 10 ≤ readTablesPrefixLen restLen := by
        simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_10 restLen
      simpa [readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen] using
        (flush_size_writeBits_prefix bw (readTablesPrefixBits restBits) 10
          (readTablesPrefixLen restLen) hk))
    (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 10 hbit)

private def readTablesPrefixWriter14
    (bw : BitWriter) (restBits : Nat) : BitWriter :=
  BitWriter.writeBits bw (readTablesPrefixBits restBits) 14

private def readTablesPrefixReader14
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt (readTablesPrefixWriter14 bw restBits)
    (readTablesPrefixWriter bw restBits restLen).flush
    (by
      have hk : 14 ≤ readTablesPrefixLen restLen := by
        simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_14 restLen
      simpa [readTablesPrefixWriter14, readTablesPrefixWriter,
        readTablesPrefixBits, readTablesPrefixLen] using
        (flush_size_writeBits_prefix bw (readTablesPrefixBits restBits) 14
          (readTablesPrefixLen restLen) hk))
    (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 14 hbit)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
private lemma readTablesPrefixReader_bound5
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) :
    (readTablesPrefixReader bw restBits restLen hbit).bitIndex + 5 ≤
      (readTablesPrefixReader bw restBits restLen hbit).data.size * 8 := by
  have hk : 5 ≤ readTablesPrefixLen restLen := by
    simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_5 restLen
  simpa [readTablesPrefixReader, readTablesPrefixWriter,
    readTablesPrefixBits, readTablesPrefixLen] using
    (readerAt_writeBits_bound
      (bw := bw) (bits := readTablesPrefixBits restBits)
      (len := readTablesPrefixLen restLen) (k := 5) hk hbit)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
private lemma readTablesPrefixWriter_eq_split5
    (bw : BitWriter) (restBits restLen : Nat) :
    readTablesPrefixWriter bw restBits restLen =
      BitWriter.writeBits
        (BitWriter.writeBits bw (readTablesPrefixBits restBits) 5)
        (readTablesPrefixBits restBits >>> 5)
        (readTablesPrefixLen restLen - 5) := by
  have hk5 : 5 ≤ readTablesPrefixLen restLen := by
    simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_5 restLen
  calc
    readTablesPrefixWriter bw restBits restLen =
        BitWriter.writeBits bw (readTablesPrefixBits restBits)
          (5 + (readTablesPrefixLen restLen - 5)) := by
            simp [readTablesPrefixWriter, Nat.add_sub_of_le hk5]
    _ =
        BitWriter.writeBits
          (BitWriter.writeBits bw (readTablesPrefixBits restBits) 5)
          (readTablesPrefixBits restBits >>> 5)
          (readTablesPrefixLen restLen - 5) := by
            simpa using
              writeBits_split bw (readTablesPrefixBits restBits) 5
                (readTablesPrefixLen restLen - 5)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
private lemma readTablesPrefixReader5_bound5
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) :
    (readTablesPrefixReader5 bw restBits restLen hbit).bitIndex + 5 ≤
      (readTablesPrefixReader5 bw restBits restLen hbit).data.size * 8 := by
  have hk : 5 ≤ readTablesPrefixLen restLen - 5 := by
    simpa [readTablesPrefixLen] using dynamicHeaderReadLen_sub5_ge_5 restLen
  have hflush5 :
      (BitWriter.writeBits
        (BitWriter.writeBits bw (readTablesPrefixBits restBits) 5)
        (readTablesPrefixBits restBits >>> 5)
        (readTablesPrefixLen restLen - 5)).flush =
        (readTablesPrefixWriter bw restBits restLen).flush := by
    exact
      congrArg BitWriter.flush
        (readTablesPrefixWriter_eq_split5 (bw := bw) (restBits := restBits) (restLen := restLen)).symm
  let bw5 := BitWriter.writeBits bw (readTablesPrefixBits restBits) 5
  let bwRest5 :=
    BitWriter.writeBits bw5 (readTablesPrefixBits restBits >>> 5) (readTablesPrefixLen restLen - 5)
  have hreader5 :
      BitWriter.readerAt bw5 bwRest5.flush
          (flush_size_writeBits_le bw5 (readTablesPrefixBits restBits >>> 5)
            (readTablesPrefixLen restLen - 5))
          (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 5 hbit) =
        BitWriter.readerAt bw5 (readTablesPrefixWriter bw restBits restLen).flush
          (by
            have hk5 : 5 ≤ readTablesPrefixLen restLen := by
              simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_5 restLen
            simpa [readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen] using
              (flush_size_writeBits_prefix bw (readTablesPrefixBits restBits) 5
                (readTablesPrefixLen restLen) hk5))
          (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 5 hbit) := by
    apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush5)
  have hbound' :
      (BitWriter.writeBits bw (readTablesPrefixBits restBits) 5).bitCount + 5 ≤
        (BitWriter.readerAt
          (BitWriter.writeBits bw (readTablesPrefixBits restBits) 5)
          (readTablesPrefixWriter bw restBits restLen).flush
          (by
            have hk5 : 5 ≤ readTablesPrefixLen restLen := by
              simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_5 restLen
            simpa [readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen] using
              (flush_size_writeBits_prefix bw (readTablesPrefixBits restBits) 5
                (readTablesPrefixLen restLen) hk5))
          (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 5 hbit)).data.size * 8 := by
    rw [← hreader5]
    simpa [bw5, bwRest5] using
      (readerAt_writeBits_bound
        (bw := BitWriter.writeBits bw (readTablesPrefixBits restBits) 5)
        (bits := readTablesPrefixBits restBits >>> 5)
        (len := readTablesPrefixLen restLen - 5) (k := 5) hk
        (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 5 hbit))
  simpa [readTablesPrefixReader5, readTablesPrefixWriter,
    readTablesPrefixBits, readTablesPrefixLen] using hbound'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
private lemma readTablesPrefixWriter_eq_split10
    (bw : BitWriter) (restBits restLen : Nat) :
    readTablesPrefixWriter bw restBits restLen =
      BitWriter.writeBits
        (BitWriter.writeBits bw (readTablesPrefixBits restBits) 10)
        (readTablesPrefixBits restBits >>> 10)
        (readTablesPrefixLen restLen - 10) := by
  have hk10 : 10 ≤ readTablesPrefixLen restLen := by
    simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_10 restLen
  calc
    readTablesPrefixWriter bw restBits restLen =
        BitWriter.writeBits bw (readTablesPrefixBits restBits)
          (10 + (readTablesPrefixLen restLen - 10)) := by
            simp [readTablesPrefixWriter, Nat.add_sub_of_le hk10]
    _ =
        BitWriter.writeBits
          (BitWriter.writeBits bw (readTablesPrefixBits restBits) 10)
          (readTablesPrefixBits restBits >>> 10)
          (readTablesPrefixLen restLen - 10) := by
            simpa using
              writeBits_split bw (readTablesPrefixBits restBits) 10
                (readTablesPrefixLen restLen - 10)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
private lemma readTablesPrefixReader10_bound4
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) :
    (readTablesPrefixReader10 bw restBits restLen hbit).bitIndex + 4 ≤
      (readTablesPrefixReader10 bw restBits restLen hbit).data.size * 8 := by
  have hk : 4 ≤ readTablesPrefixLen restLen - 10 := by
    simpa [readTablesPrefixLen] using dynamicHeaderReadLen_sub10_ge_4 restLen
  have hflush10 :
      (BitWriter.writeBits
        (BitWriter.writeBits bw (readTablesPrefixBits restBits) 10)
        (readTablesPrefixBits restBits >>> 10)
        (readTablesPrefixLen restLen - 10)).flush =
        (readTablesPrefixWriter bw restBits restLen).flush := by
    exact
      congrArg BitWriter.flush
        (readTablesPrefixWriter_eq_split10 (bw := bw) (restBits := restBits) (restLen := restLen)).symm
  let bw10 := BitWriter.writeBits bw (readTablesPrefixBits restBits) 10
  let bwRest10 :=
    BitWriter.writeBits bw10 (readTablesPrefixBits restBits >>> 10) (readTablesPrefixLen restLen - 10)
  have hreader10 :
      BitWriter.readerAt bw10 bwRest10.flush
          (flush_size_writeBits_le bw10 (readTablesPrefixBits restBits >>> 10)
            (readTablesPrefixLen restLen - 10))
          (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 10 hbit) =
        BitWriter.readerAt bw10 (readTablesPrefixWriter bw restBits restLen).flush
          (by
            have hk10 : 10 ≤ readTablesPrefixLen restLen := by
              simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_10 restLen
            simpa [readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen] using
              (flush_size_writeBits_prefix bw (readTablesPrefixBits restBits) 10
                (readTablesPrefixLen restLen) hk10))
          (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 10 hbit) := by
    apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush10)
  have hbound' :
      (BitWriter.writeBits bw (readTablesPrefixBits restBits) 10).bitCount + 4 ≤
        (BitWriter.readerAt
          (BitWriter.writeBits bw (readTablesPrefixBits restBits) 10)
          (readTablesPrefixWriter bw restBits restLen).flush
          (by
            have hk10 : 10 ≤ readTablesPrefixLen restLen := by
              simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_10 restLen
            simpa [readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen] using
              (flush_size_writeBits_prefix bw (readTablesPrefixBits restBits) 10
                (readTablesPrefixLen restLen) hk10))
          (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 10 hbit)).data.size * 8 := by
    rw [← hreader10]
    simpa [bw10, bwRest10] using
      (readerAt_writeBits_bound
        (bw := BitWriter.writeBits bw (readTablesPrefixBits restBits) 10)
        (bits := readTablesPrefixBits restBits >>> 10)
        (len := readTablesPrefixLen restLen - 10) (k := 4) hk
        (bitPos_lt_8_writeBits bw (readTablesPrefixBits restBits) 10 hbit))
  simpa [readTablesPrefixReader10, readTablesPrefixWriter,
    readTablesPrefixBits, readTablesPrefixLen] using hbound'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Shows that the first five dynamic-header bits decode the expected `HLIT` value from the writer stream. -/
lemma readDynamicTablesPrefix_hlit_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (readTablesPrefixReader bw restBits restLen hbit).readBits 5
        (readTablesPrefixReader_bound5 bw restBits restLen hbit) =
      (31, readTablesPrefixReader5 bw restBits restLen hbit) := by
  have hstep :=
    readBits_readerAt_writeBits_shift
      (bw := bw) (bits := readTablesPrefixBits restBits) (len := readTablesPrefixLen restLen)
      (skip := 0) (k := 5)
      (by omega)
      (by simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_5 restLen)
      hbit hcur
  have hmod : (readTablesPrefixBits restBits >>> 0) % 2 ^ 5 = 31 := by
    simpa [readTablesPrefixBits] using dynamicHeaderReadBits_low5 restBits
  have hstep' :
      (readTablesPrefixReader bw restBits restLen hbit).readBits 5
          (readTablesPrefixReader_bound5 bw restBits restLen hbit) =
        (((readTablesPrefixBits restBits >>> 0) % 2 ^ 5),
          readTablesPrefixReader5 bw restBits restLen hbit) := by
    simpa [readTablesPrefixReader, readTablesPrefixReader5,
      readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen] using hstep
  rw [hmod] at hstep'
  exact hstep'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Shows that the next five dynamic-header bits decode the expected `HDIST` value from the writer stream. -/
lemma readDynamicTablesPrefix_hdist_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (readTablesPrefixReader5 bw restBits restLen hbit).readBits 5
        (readTablesPrefixReader5_bound5 bw restBits restLen hbit) =
      (31, readTablesPrefixReader10 bw restBits restLen hbit) := by
  have hstep :=
    readBits_readerAt_writeBits_shift
      (bw := bw) (bits := readTablesPrefixBits restBits) (len := readTablesPrefixLen restLen)
      (skip := 5) (k := 5)
      (by simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_5 restLen)
      (by simpa [readTablesPrefixLen] using dynamicHeaderReadLen_sub5_ge_5 restLen)
      hbit hcur
  have hmod : (readTablesPrefixBits restBits >>> 5) % 2 ^ 5 = 31 := by
    simpa [readTablesPrefixBits] using dynamicHeaderReadBits_mid5 restBits
  have hflush5 :
      (BitWriter.writeBits
        (BitWriter.writeBits bw (readTablesPrefixBits restBits) 5)
        (readTablesPrefixBits restBits >>> 5)
        (readTablesPrefixLen restLen - 5)).flush =
        (readTablesPrefixWriter bw restBits restLen).flush := by
    exact
      congrArg BitWriter.flush
        (readTablesPrefixWriter_eq_split5 (bw := bw) (restBits := restBits) (restLen := restLen)).symm
  have hstep' :
      (readTablesPrefixReader5 bw restBits restLen hbit).readBits 5
          (readTablesPrefixReader5_bound5 bw restBits restLen hbit) =
        (((readTablesPrefixBits restBits >>> 5) % 2 ^ 5),
          readTablesPrefixReader10 bw restBits restLen hbit) := by
    simpa [readTablesPrefixReader5, readTablesPrefixReader10,
      readTablesPrefixWriter, readTablesPrefixBits, readTablesPrefixLen, hflush5] using hstep
  rw [hmod] at hstep'
  exact hstep'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Shows that the final four prefix bits decode the expected `HCLEN` value from the writer stream. -/
lemma readDynamicTablesPrefix_hclen_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (readTablesPrefixReader10 bw restBits restLen hbit).readBits 4
        (readTablesPrefixReader10_bound4 bw restBits restLen hbit) =
      (6, readTablesPrefixReader14 bw restBits restLen hbit) := by
  have hstep :=
    readBits_readerAt_writeBits_shift
      (bw := bw) (bits := readTablesPrefixBits restBits) (len := readTablesPrefixLen restLen)
      (skip := 10) (k := 4)
      (by simpa [readTablesPrefixLen] using dynamicHeaderReadLen_ge_10 restLen)
      (by simpa [readTablesPrefixLen] using dynamicHeaderReadLen_sub10_ge_4 restLen)
      hbit hcur
  have hmod : (readTablesPrefixBits restBits >>> 10) % 2 ^ 4 = 6 := by
    simpa [readTablesPrefixBits] using dynamicHeaderReadBits_high4 restBits
  have hflush10 :
      (BitWriter.writeBits
        (BitWriter.writeBits bw (readTablesPrefixBits restBits) 10)
        (readTablesPrefixBits restBits >>> 10)
        (readTablesPrefixLen restLen - 10)).flush =
        (readTablesPrefixWriter bw restBits restLen).flush := by
    exact
      congrArg BitWriter.flush
        (readTablesPrefixWriter_eq_split10 (bw := bw) (restBits := restBits) (restLen := restLen)).symm
  have hstep' :
      (readTablesPrefixReader10 bw restBits restLen hbit).readBits 4
          (readTablesPrefixReader10_bound4 bw restBits restLen hbit) =
        (((readTablesPrefixBits restBits >>> 10) % 2 ^ 4),
          readTablesPrefixReader14 bw restBits restLen hbit) := by
    simpa [readTablesPrefixReader10, readTablesPrefixReader14,
      readTablesPrefixWriter14, readTablesPrefixWriter,
      readTablesPrefixBits, readTablesPrefixLen, hflush10] using hstep
  rw [hmod] at hstep'
  exact hstep'

end Png

end Bitmaps
