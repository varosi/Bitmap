import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesReaderTransportLeftHelpers

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
/-- Identifies the post-header reader with the reader after consuming the first 44 header bits. -/
lemma dynamicTablesAfterHeaderReaderAt_eq_writeBits44Reader
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
    dynamicTablesAfterHeaderReader bw restBits restLen hbit =
      dynamicTables44Reader bw restBits restLen hbit := by
  unfold dynamicTablesAfterHeaderReader
  unfold dynamicTablesAfterHeaderReaderAt dynamicCodeLenSymsReaderAt
  unfold dynamicTables44Reader
  apply readerAt_eq_of_eqs
  · simpa using
      (dynamicTablesAfterHeaderPrefix_eq_dynamicTables44PrefixWriter
        (bw := bw) (restBits := restBits))
  · simpa using
      congrArg BitWriter.flush
        (dynamicTablesAfterHeaderFull_eq_dynamicTablesAfterHeaderBwFull
          (bw := bw) (restBits := restBits) (restLen := restLen))

end Png

end Bitmaps
