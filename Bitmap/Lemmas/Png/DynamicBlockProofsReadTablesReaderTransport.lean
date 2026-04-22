import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesReaderTransportLeft

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Composes the left and right reader transports into one reusable post-header reader equality. -/
lemma dynamicTablesAfterHeaderReaderAt_eq_dynamicTablesReaderAt
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
    let bitsTot := dynamicHeaderReadBits restBits
    let bw14 := BitWriter.writeBits bw bitsTot 14
    dynamicTablesAfterHeaderReaderAt bw14 restBits restLen
        (bitPos_lt_8_writeBits bw bitsTot 14 hbit) =
      dynamicTablesReaderAt bw restBits restLen hbit := by
  let bitsTot := dynamicHeaderReadBits restBits
  let bw14 := BitWriter.writeBits bw bitsTot 14
  calc
    dynamicTablesAfterHeaderReaderAt bw14 restBits restLen
        (bitPos_lt_8_writeBits bw bitsTot 14 hbit) =
      dynamicTablesAfterHeaderReader bw restBits restLen hbit := by
        simp [dynamicTablesAfterHeaderReader, bitsTot, bw14]
    _ = dynamicTables44Reader bw restBits restLen hbit := by
      exact dynamicTablesAfterHeaderReaderAt_eq_writeBits44Reader
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit
    _ = dynamicTablesReaderAt bw restBits restLen hbit := by
      exact writeBits44Reader_eq_dynamicTablesReaderAt
          (bw := bw) (restBits := restBits) (restLen := restLen) hbit

end Png

end Bitmaps
