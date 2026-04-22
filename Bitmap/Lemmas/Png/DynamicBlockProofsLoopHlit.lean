import Bitmap.Lemmas.Png.DynamicBlockProofsLoopBase

namespace Bitmaps

namespace Lemmas

open Png

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Evaluates the dynamic stream's first header read and shows it returns the fixed `HLIT` value. -/
lemma readDynamicTables_hlit_dynamicStream (raw : ByteArray) :
    let payloadBits := fixedLitBitsEob raw.data 0
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
    let streamReaderHeader := BitWriter.readerAt hdrHeader
      (BitWriter.writeBits hdrHeader bitsTot lenTot).flush
      (flush_size_writeBits_le hdrHeader bitsTot lenTot)
      hbitHeader
    streamReaderHeader.readBits 5
        (by
          have hk : 5 ≤ lenTot := by
            simpa [lenTot] using dynamicHeaderReadLen_ge_5 payloadBits.2
          simpa [streamReaderHeader, bw', lenTot] using
            (readerAt_writeBits_bound
              (bw := hdrHeader) (bits := bitsTot) (len := lenTot) (k := 5) hk hbitHeader)) =
      (31, br5) := by
  let payloadBits := fixedLitBitsEob raw.data 0
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
  let streamReaderHeader := BitWriter.readerAt hdrHeader
    (BitWriter.writeBits hdrHeader bitsTot lenTot).flush
    (flush_size_writeBits_le hdrHeader bitsTot lenTot)
    hbitHeader
  simpa [bitsTot, lenTot, bw', br5, streamReaderHeader] using
    (readDynamicTables_hlit_readerAt_writeBits
      (bw := hdrHeader) (restBits := payloadBits.1) (restLen := payloadBits.2)
      hbitHeader hcurHeader)

end Lemmas

end Bitmaps
