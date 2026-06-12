import Bitmap.Lemmas.Png.DynamicBlockProofsLoopBase

namespace Bitmaps

namespace Lemmas

open Png

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Evaluates the dynamic stream's third header read and shows it returns the fixed `HCLEN` value. -/
lemma readDynamicTables_hclen_dynamicStream (raw : ByteArray) :
    let payloadBits := dynamicStreamPayloadBits raw
    let hdr0 := BitWriter.empty
    let hdrHeader := BitWriter.writeBits hdr0 5 3
    let bitsTot := dynamicHeaderReadBits payloadBits.1
    let lenTot := dynamicHeaderReadLen payloadBits.2
    let hbitHeader : hdrHeader.bitPos < 8 := by
      simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
    let hcur0 : hdr0.curClearAbove := curClearAbove_empty
    let hcurHeader : hdrHeader.curClearAbove := by
      simpa [hdrHeader] using curClearAbove_writeBits hdr0 5 3 (by decide) hcur0
    let bw' := BitWriter.writeBits hdrHeader bitsTot lenTot
    let br10 := BitWriter.readerAt (BitWriter.writeBits hdrHeader bitsTot 10) bw'.flush
      (by
        have hk : 10 ≤ lenTot := by
          simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
        simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 10 lenTot hk)
      (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)
    let bw14 := BitWriter.writeBits hdrHeader bitsTot 14
    let br14 := BitWriter.readerAt bw14 bw'.flush
      (by
        have hk : 14 ≤ lenTot := by
          simpa [lenTot] using dynamicHeaderReadLen_ge_14 payloadBits.2
        simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 14 lenTot hk)
      (bitPos_lt_8_writeBits hdrHeader bitsTot 14 hbitHeader)
    br10.readBits 4
        (by
          have hk : 4 ≤ lenTot - 10 := by
            simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 payloadBits.2
          let bw10 := BitWriter.writeBits hdrHeader bitsTot 10
          let bwRest10 := BitWriter.writeBits bw10 (bitsTot >>> 10) (lenTot - 10)
          have hflush10 : bwRest10.flush = bw'.flush := by
            calc
              bwRest10.flush =
                  (BitWriter.writeBits
                    (BitWriter.writeBits hdrHeader bitsTot 10)
                    (bitsTot >>> 10)
                    (lenTot - 10)).flush := by
                      simp [bw10, bwRest10]
              _ = bw'.flush := by
                  have hsplit :
                      bw' =
                        BitWriter.writeBits
                          (BitWriter.writeBits hdrHeader bitsTot 10)
                          (bitsTot >>> 10)
                          (lenTot - 10) := by
                        have hk10 : 10 ≤ lenTot := by
                          simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
                        calc
                          bw' = BitWriter.writeBits hdrHeader bitsTot (10 + (lenTot - 10)) := by
                            simp [bw', Nat.add_sub_of_le hk10]
                          _ =
                              BitWriter.writeBits
                                (BitWriter.writeBits hdrHeader bitsTot 10)
                                (bitsTot >>> 10)
                                (lenTot - 10) := by
                                  simpa using writeBits_split hdrHeader bitsTot 10 (lenTot - 10)
                  simpa [bw'] using congrArg BitWriter.flush hsplit.symm
          have hreader10 :
              BitWriter.readerAt bw10 bwRest10.flush
                  (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader) =
                BitWriter.readerAt bw10 bw'.flush
                  (by
                    have hk10 : 10 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
                    simpa [bw', lenTot] using
                      flush_size_writeBits_prefix hdrHeader bitsTot 10 lenTot hk10)
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader) := by
            apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush10)
          have hboundSplit :
              (BitWriter.readerAt bw10 bwRest10.flush
                  (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)).bitIndex + 4 ≤
                (BitWriter.readerAt bw10 bwRest10.flush
                  (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)).data.size * 8 := by
            simpa [bw10, bwRest10] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits hdrHeader bitsTot 10)
                (bits := bitsTot >>> 10) (len := lenTot - 10)
                (k := 4) hk (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader))
          have hboundFull :
              (BitWriter.readerAt bw10 bw'.flush
                  (by
                    have hk10 : 10 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
                    simpa [bw', lenTot] using
                      flush_size_writeBits_prefix hdrHeader bitsTot 10 lenTot hk10)
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)).bitIndex + 4 ≤
                (BitWriter.readerAt bw10 bw'.flush
                  (by
                    have hk10 : 10 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
                    simpa [bw', lenTot] using
                      flush_size_writeBits_prefix hdrHeader bitsTot 10 lenTot hk10)
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)).data.size * 8 := by
            rw [← hreader10]
            exact hboundSplit
          simpa [br10, bw10] using hboundFull) =
      (6, br14) := by
  let payloadBits := dynamicStreamPayloadBits raw
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let bitsTot := dynamicHeaderReadBits payloadBits.1
  let lenTot := dynamicHeaderReadLen payloadBits.2
  have hbitHeader : hdrHeader.bitPos < 8 := by
    simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
  have hcur0 : hdr0.curClearAbove := curClearAbove_empty
  have hcurHeader : hdrHeader.curClearAbove := by
    simpa [hdrHeader] using curClearAbove_writeBits hdr0 5 3 (by decide) hcur0
  let bw' := BitWriter.writeBits hdrHeader bitsTot lenTot
  let br10 := BitWriter.readerAt (BitWriter.writeBits hdrHeader bitsTot 10) bw'.flush
    (by
      have hk : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
      simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 10 lenTot hk)
    (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)
  let bw14 := BitWriter.writeBits hdrHeader bitsTot 14
  let br14 := BitWriter.readerAt bw14 bw'.flush
    (by
      have hk : 14 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_14 payloadBits.2
      simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 14 lenTot hk)
    (bitPos_lt_8_writeBits hdrHeader bitsTot 14 hbitHeader)
  simpa [bitsTot, lenTot, bw', br10, bw14, br14] using
    (readDynamicTables_hclen_readerAt_writeBits
      (bw := hdrHeader) (restBits := payloadBits.1) (restLen := payloadBits.2)
      hbitHeader hcurHeader)

end Lemmas

end Bitmaps
