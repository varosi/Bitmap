import Bitmap.Lemmas.Png.DynamicBlockProofsLoopAfterHeader
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesConcrete
import Bitmap.Lemmas.Png.DynamicBlockProofsSpec

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

/-- Repackages the concrete dynamic-fast table read as a generic `DynamicTableSpec` witness,
showing the concrete proof path now factors through the generalized read-table layer. -/
lemma readDynamicTables_dynamicStream_spec (raw : ByteArray) :
    ∃ spec,
      readDynamicTablesSpec? (dynamicStreamReaderHeader raw) =
        some (spec, dynamicStreamPayloadReaderStart raw) ∧
        spec.litLenTable = fixedLitLenHuffman ∧
        spec.distTable = fixedDistHuffman := by
  simpa using
    (Png.readDynamicTables_exists_spec
      (br := dynamicStreamReaderHeader raw)
      (litLenTable := fixedLitLenHuffman)
      (distTable := fixedDistHuffman)
      (br' := dynamicStreamPayloadReaderStart raw)
      (readDynamicTables_dynamicStream raw))

end Lemmas

end Bitmaps
