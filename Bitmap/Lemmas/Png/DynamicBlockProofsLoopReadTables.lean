import Bitmap.Lemmas.Png.DynamicBlockProofsLoopAfterHeader
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesConcrete

namespace Bitmaps

namespace Lemmas

open Png

def dynamicStreamReaderHeader (raw : ByteArray) : BitReader :=
  BitWriter.readerAt dynamicStreamHdrHeader (dynamicStreamBwPrime raw).flush
    (flush_size_writeBits_le dynamicStreamHdrHeader
      (dynamicStreamBitsTot raw) (dynamicStreamLenTot raw))
    dynamicStreamHdrHeader_bitPos_lt

set_option maxRecDepth 400000 in
set_option maxHeartbeats 20000000 in
/-- Replays the full `readDynamicTables` front-end directly on the concrete dynamic fast stream. -/
lemma readDynamicTables_dynamicStream (raw : ByteArray) :
    readDynamicTables (dynamicStreamReaderHeader raw) =
      some (fixedLitLenHuffman, fixedDistHuffman, dynamicStreamPayloadReaderStart raw) := by
  have hcore :=
    Png.readDynamicTables_readerAt_writeBits_concrete
      (bw := dynamicStreamHdrHeader)
      (restBits := (dynamicStreamPayloadBits raw).1)
      (restLen := (dynamicStreamPayloadBits raw).2)
      dynamicStreamHdrHeader_bitPos_lt
      dynamicStreamHdrHeader_curClearAbove
  have hcore' :
      readDynamicTables (dynamicStreamReaderHeader raw) =
        some (fixedLitLenHuffman, fixedDistHuffman, dynamicStreamAfterHeaderReader raw) := by
    simpa [dynamicStreamReaderHeader, dynamicStreamPayloadBits, dynamicStreamBitsTot,
      dynamicStreamLenTot, dynamicStreamBwPrime, dynamicStreamBw14, dynamicStreamAfterHeaderReader]
      using hcore
  calc
    readDynamicTables (dynamicStreamReaderHeader raw) =
        some (fixedLitLenHuffman, fixedDistHuffman, dynamicStreamAfterHeaderReader raw) := hcore'
    _ = some (fixedLitLenHuffman, fixedDistHuffman, dynamicStreamPayloadReaderStart raw) := by
      simp [dynamicTablesAfterHeader_dynamicStream_readerEq raw]

end Lemmas

end Bitmaps
