import Bitmap.Lemmas.Png.DynamicBlockProofsLoopBase

namespace Bitmaps

namespace Lemmas

open Png

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Evaluates the dynamic stream's second header read and shows it returns the fixed `HDIST` value. -/
lemma readDynamicTables_hdist_dynamicStream (raw : ByteArray) :
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
    let br5 := BitWriter.readerAt (BitWriter.writeBits hdrHeader bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by
          simpa [lenTot] using dynamicHeaderReadLen_ge_5 payloadBits.2
        simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 5 lenTot hk)
      (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader)
    let br10 := BitWriter.readerAt (BitWriter.writeBits hdrHeader bitsTot 10) bw'.flush
      (by
        have hk : 10 ≤ lenTot := by
          simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
        simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 10 lenTot hk)
      (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)
    br5.readBits 5
        (by
          have hk : 5 ≤ lenTot - 5 := by
            simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 payloadBits.2
          let bw5 := BitWriter.writeBits hdrHeader bitsTot 5
          let bwRest5 := BitWriter.writeBits bw5 (bitsTot >>> 5) (lenTot - 5)
          have hflush5 : bwRest5.flush = bw'.flush := by
            calc
              bwRest5.flush =
                  (BitWriter.writeBits
                    (BitWriter.writeBits hdrHeader bitsTot 5)
                    (bitsTot >>> 5)
                    (lenTot - 5)).flush := by
                      simp [bw5, bwRest5]
              _ = bw'.flush := by
                  have hsplit :
                      bw' =
                        BitWriter.writeBits
                          (BitWriter.writeBits hdrHeader bitsTot 5)
                          (bitsTot >>> 5)
                          (lenTot - 5) := by
                        have hk5 : 5 ≤ lenTot := by
                          simpa [lenTot] using dynamicHeaderReadLen_ge_5 payloadBits.2
                        calc
                          bw' = BitWriter.writeBits hdrHeader bitsTot (5 + (lenTot - 5)) := by
                            simp [bw', Nat.add_sub_of_le hk5]
                          _ =
                              BitWriter.writeBits
                                (BitWriter.writeBits hdrHeader bitsTot 5)
                                (bitsTot >>> 5)
                                (lenTot - 5) := by
                                  simpa using writeBits_split hdrHeader bitsTot 5 (lenTot - 5)
                  simpa [bw'] using congrArg BitWriter.flush hsplit.symm
          have hreader5 :
              BitWriter.readerAt bw5 bwRest5.flush
                  (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader) =
                BitWriter.readerAt bw5 bw'.flush
                  (by
                    have hk5 : 5 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_5 payloadBits.2
                    simpa [bw', lenTot] using
                      flush_size_writeBits_prefix hdrHeader bitsTot 5 lenTot hk5)
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader) := by
            apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush5)
          have hboundSplit :
              (BitWriter.readerAt bw5 bwRest5.flush
                  (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader)).bitIndex + 5 ≤
                (BitWriter.readerAt bw5 bwRest5.flush
                  (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader)).data.size * 8 := by
            simpa [bw5, bwRest5] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBits hdrHeader bitsTot 5)
                (bits := bitsTot >>> 5) (len := lenTot - 5)
                (k := 5) hk (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader))
          have hboundFull :
              (BitWriter.readerAt bw5 bw'.flush
                  (by
                    have hk5 : 5 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_5 payloadBits.2
                    simpa [bw', lenTot] using
                      flush_size_writeBits_prefix hdrHeader bitsTot 5 lenTot hk5)
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader)).bitIndex + 5 ≤
                (BitWriter.readerAt bw5 bw'.flush
                  (by
                    have hk5 : 5 ≤ lenTot := by
                      simpa [lenTot] using dynamicHeaderReadLen_ge_5 payloadBits.2
                    simpa [bw', lenTot] using
                      flush_size_writeBits_prefix hdrHeader bitsTot 5 lenTot hk5)
                  (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader)).data.size * 8 := by
            rw [← hreader5]
            exact hboundSplit
          simpa [br5, bw5] using hboundFull) =
      (31, br10) := by
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
  let br5 := BitWriter.readerAt (BitWriter.writeBits hdrHeader bitsTot 5) bw'.flush
    (by
      have hk : 5 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_5 payloadBits.2
      simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 5 lenTot hk)
    (bitPos_lt_8_writeBits hdrHeader bitsTot 5 hbitHeader)
  let br10 := BitWriter.readerAt (BitWriter.writeBits hdrHeader bitsTot 10) bw'.flush
    (by
      have hk : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 payloadBits.2
      simpa [bw', lenTot] using flush_size_writeBits_prefix hdrHeader bitsTot 10 lenTot hk)
    (bitPos_lt_8_writeBits hdrHeader bitsTot 10 hbitHeader)
  simpa [bitsTot, lenTot, bw', br5, br10] using
    (readDynamicTables_hdist_readerAt_writeBits
      (bw := hdrHeader) (restBits := payloadBits.1) (restLen := payloadBits.2)
      hbitHeader hcurHeader)

end Lemmas

end Bitmaps
