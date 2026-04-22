import Bitmap.Lemmas.Png.DynamicBlockProofsLoopAfterHeaderReaderEq

namespace Bitmaps

namespace Lemmas

open Png

def dynamicStreamBr14 (raw : ByteArray) : BitReader :=
  BitWriter.readerAt (dynamicStreamBw14 raw) (dynamicStreamBwPrime raw).flush
    (by
      have hk : 14 ≤ dynamicStreamLenTot raw := by
        simpa [dynamicStreamLenTot, dynamicStreamPayloadBits] using
          dynamicHeaderReadLen_ge_14 (dynamicStreamPayloadBits raw).2
      simpa [dynamicStreamBwPrime, dynamicStreamLenTot] using
        flush_size_writeBits_prefix dynamicStreamHdrHeader (dynamicStreamBitsTot raw) 14
          (dynamicStreamLenTot raw) hk)
    (by
      simpa [dynamicStreamBw14, dynamicStreamHdrHeader] using
        bitPos_lt_8_writeBits dynamicStreamHdrHeader (dynamicStreamBitsTot raw) 14
          dynamicStreamHdrHeader_bitPos_lt)

/-- Supplies the bit-position invariant for the writer after the first 14 dynamic-header bits. -/
lemma dynamicStreamBw14_bitPos_lt (raw : ByteArray) :
    (dynamicStreamBw14 raw).bitPos < 8 := by
  simpa [dynamicStreamBw14, dynamicStreamHdrHeader] using
    bitPos_lt_8_writeBits dynamicStreamHdrHeader (dynamicStreamBitsTot raw) 14
      dynamicStreamHdrHeader_bitPos_lt

/-- Supplies the `curClearAbove` invariant for the writer after the first 14 dynamic-header bits. -/
lemma dynamicStreamBw14_curClearAbove (raw : ByteArray) :
    (dynamicStreamBw14 raw).curClearAbove := by
  simpa [dynamicStreamBw14, dynamicStreamHdrHeader] using
    curClearAbove_writeBits dynamicStreamHdrHeader (dynamicStreamBitsTot raw) 14
      dynamicStreamHdrHeader_bitPos_lt dynamicStreamHdrHeader_curClearAbove

def dynamicStreamBwAfterHeader (raw : ByteArray) : BitWriter :=
  BitWriter.writeBits (dynamicStreamBw14 raw)
    (dynamicHeaderCodeLenLensBits (dynamicStreamPayloadBits raw).1)
    (dynamicHeaderCodeLenLensLen (dynamicStreamPayloadBits raw).2)

/-- Rewrites the staged writer after the table section back to the canonical dynamic stream writer. -/
lemma dynamicStreamBwAfterHeader_eq_bwPrime (raw : ByteArray) :
    dynamicStreamBwAfterHeader raw = dynamicStreamBwPrime raw := by
  have hk14 : 14 ≤ dynamicStreamLenTot raw := by
    simpa [dynamicStreamLenTot, dynamicStreamPayloadBits] using
      dynamicHeaderReadLen_ge_14 (dynamicStreamPayloadBits raw).2
  calc
    dynamicStreamBwAfterHeader raw =
      BitWriter.writeBits (dynamicStreamBw14 raw)
        ((dynamicStreamBitsTot raw) >>> 14)
        (dynamicStreamLenTot raw - 14) := by
          simp [dynamicStreamBwAfterHeader, dynamicStreamPayloadBits,
            dynamicStreamBitsTot, dynamicStreamLenTot,
            dynamicHeaderReadBits_shift14, dynamicHeaderReadLen_sub14]
    _ = dynamicStreamBwPrime raw := by
          calc
            BitWriter.writeBits (dynamicStreamBw14 raw)
                ((dynamicStreamBitsTot raw) >>> 14)
                (dynamicStreamLenTot raw - 14) =
              BitWriter.writeBits dynamicStreamHdrHeader (dynamicStreamBitsTot raw)
                (14 + (dynamicStreamLenTot raw - 14)) := by
                  symm
                  simpa [dynamicStreamBw14] using
                    (writeBits_split dynamicStreamHdrHeader (dynamicStreamBitsTot raw) 14
                      (dynamicStreamLenTot raw - 14))
            _ = dynamicStreamBwPrime raw := by
                  simp [dynamicStreamBwPrime, Nat.add_sub_of_le hk14]

/-- Identifies the cached reader after 14 bits with the reader built from the staged writer proof. -/
lemma dynamicStreamBr14_eq_readerAt_afterHeader (raw : ByteArray) :
    dynamicStreamBr14 raw =
      BitWriter.readerAt (dynamicStreamBw14 raw) (dynamicStreamBwAfterHeader raw).flush
        (flush_size_writeBits_le (dynamicStreamBw14 raw)
          (dynamicHeaderCodeLenLensBits (dynamicStreamPayloadBits raw).1)
          (dynamicHeaderCodeLenLensLen (dynamicStreamPayloadBits raw).2))
        (dynamicStreamBw14_bitPos_lt raw) := by
  apply readerAt_eq_of_eqs (hbw := rfl)
  · exact congrArg BitWriter.flush (dynamicStreamBwAfterHeader_eq_bwPrime raw).symm

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Proves that the dynamic stream's post-header table section decodes to the fixed runtime tables. -/
lemma readDynamicTablesAfterHeader_dynamicStream (raw : ByteArray) :
    readDynamicTablesAfterHeader (dynamicStreamBr14 raw) =
      some (fixedLitLenHuffman, fixedDistHuffman, dynamicStreamPayloadReaderStart raw) := by
  have hafterHeader0 :
      readDynamicTablesAfterHeader (dynamicStreamBr14 raw) =
        some
          (fixedLitLenHuffman, fixedDistHuffman, dynamicStreamAfterHeaderReader raw) := by
    have hcore := readDynamicTablesAfterHeader_readerAt_writeBits
        (bw := dynamicStreamBw14 raw)
        (restBits := (dynamicStreamPayloadBits raw).1)
        (restLen := (dynamicStreamPayloadBits raw).2)
        (dynamicStreamBw14_bitPos_lt raw)
        (dynamicStreamBw14_curClearAbove raw)
    rw [dynamicStreamBr14_eq_readerAt_afterHeader raw]
    simpa [dynamicStreamAfterHeaderReader, dynamicStreamBwAfterHeader, dynamicStreamPayloadBits] using
      hcore
  have hreader :
      dynamicStreamAfterHeaderReader raw =
        dynamicStreamPayloadReaderStart raw := by
    exact dynamicTablesAfterHeader_dynamicStream_readerEq raw
  simpa [hreader] using hafterHeader0

end Lemmas

end Bitmaps
