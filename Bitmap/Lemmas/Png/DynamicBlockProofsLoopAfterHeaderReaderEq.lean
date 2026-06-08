import Bitmap.Lemmas.Png.DynamicBlockProofsLoopBase
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesReaderTransport

namespace Bitmaps

namespace Lemmas

open Png

def dynamicStreamPayloadBits (raw : ByteArray) : Nat × Nat :=
  fixedLitBitsEob raw.data 0

def dynamicStreamHdr0 : BitWriter :=
  BitWriter.empty

def dynamicStreamHdrHeader : BitWriter :=
  BitWriter.writeBits dynamicStreamHdr0 5 3

/-- Records the bit-position invariant for the synthetic writer used to model the dynamic stream header. -/
lemma dynamicStreamHdrHeader_bitPos_lt : dynamicStreamHdrHeader.bitPos < 8 := by
  simpa [dynamicStreamHdrHeader, dynamicStreamHdr0] using
    bitPos_lt_8_writeBits BitWriter.empty 5 3 (by decide)

/-- Records the `curClearAbove` invariant for the synthetic writer used to model the dynamic stream header. -/
lemma dynamicStreamHdrHeader_curClearAbove : dynamicStreamHdrHeader.curClearAbove := by
  simpa [dynamicStreamHdrHeader, dynamicStreamHdr0] using
    curClearAbove_writeBits BitWriter.empty 5 3 (by decide) curClearAbove_empty

def dynamicStreamBitsTot (raw : ByteArray) : Nat :=
  dynamicHeaderReadBits (dynamicStreamPayloadBits raw).1

def dynamicStreamLenTot (raw : ByteArray) : Nat :=
  dynamicHeaderReadLen (dynamicStreamPayloadBits raw).2

def dynamicStreamBwPrime (raw : ByteArray) : BitWriter :=
  BitWriter.writeBits dynamicStreamHdrHeader (dynamicStreamBitsTot raw) (dynamicStreamLenTot raw)

def dynamicStreamBwTables : BitWriter :=
  BitWriter.writeBits dynamicStreamHdrHeader dynamicHeaderTableBits dynamicHeaderTableLen

def dynamicStreamWriter (raw : ByteArray) : BitWriter :=
  BitWriter.writeBits dynamicStreamBwTables (dynamicStreamPayloadBits raw).1 (dynamicStreamPayloadBits raw).2

def dynamicStreamPayloadReaderStart (raw : ByteArray) : BitReader :=
  BitWriter.readerAt dynamicStreamBwTables (dynamicStreamWriter raw).flush
    (flush_size_writeBits_le dynamicStreamBwTables
      (dynamicStreamPayloadBits raw).1 (dynamicStreamPayloadBits raw).2)
    (by
      simpa [dynamicStreamBwTables, dynamicStreamHdrHeader] using
        bitPos_lt_8_writeBits dynamicStreamHdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
          dynamicStreamHdrHeader_bitPos_lt)

def dynamicStreamBw14 (raw : ByteArray) : BitWriter :=
  BitWriter.writeBits dynamicStreamHdrHeader (dynamicStreamBitsTot raw) 14

def dynamicStreamAfterHeaderReader (raw : ByteArray) : BitReader :=
  dynamicTablesAfterHeaderReaderAt (dynamicStreamBw14 raw)
    (dynamicStreamPayloadBits raw).1 (dynamicStreamPayloadBits raw).2
    (by
      simpa [dynamicStreamBw14, dynamicStreamHdrHeader] using
        bitPos_lt_8_writeBits dynamicStreamHdrHeader (dynamicStreamBitsTot raw) 14
          dynamicStreamHdrHeader_bitPos_lt)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Matches the reader after the dynamic table section with the reader derived from the raw stream writer. -/
lemma dynamicTablesAfterHeader_dynamicStream_readerEq (raw : ByteArray) :
    dynamicStreamAfterHeaderReader raw =
      dynamicStreamPayloadReaderStart raw := by
  have hreader0 :
      dynamicStreamAfterHeaderReader raw =
        dynamicTablesReaderAt dynamicStreamHdrHeader
          (dynamicStreamPayloadBits raw).1 (dynamicStreamPayloadBits raw).2
          dynamicStreamHdrHeader_bitPos_lt := by
    simpa [dynamicStreamAfterHeaderReader, dynamicStreamPayloadBits, dynamicStreamBitsTot,
      dynamicStreamLenTot, dynamicStreamBwPrime, dynamicStreamBw14] using
      (Png.dynamicTablesAfterHeaderReaderAt_eq_dynamicTablesReaderAt
        (bw := dynamicStreamHdrHeader)
        (restBits := (dynamicStreamPayloadBits raw).1)
        (restLen := (dynamicStreamPayloadBits raw).2)
        dynamicStreamHdrHeader_bitPos_lt)
  calc
    dynamicStreamAfterHeaderReader raw =
        dynamicTablesReaderAt dynamicStreamHdrHeader
          (dynamicStreamPayloadBits raw).1 (dynamicStreamPayloadBits raw).2
          dynamicStreamHdrHeader_bitPos_lt := hreader0
    _ = dynamicStreamPayloadReaderStart raw := by
      simpa [dynamicStreamPayloadReaderStart, dynamicStreamPayloadBits, dynamicStreamWriter,
        dynamicStreamBwTables] using
        (dynamicTablesReaderAt_eq_payloadReader
          (bw := dynamicStreamHdrHeader)
          (restBits := (dynamicStreamPayloadBits raw).1)
          (restLen := (dynamicStreamPayloadBits raw).2)
          dynamicStreamHdrHeader_bitPos_lt)

end Lemmas

end Bitmaps
