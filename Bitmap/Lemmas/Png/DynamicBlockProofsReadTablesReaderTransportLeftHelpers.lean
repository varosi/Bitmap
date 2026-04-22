import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesReaderTransportBase

namespace Bitmaps

namespace Png

def dynamicTablesAfterHeaderReader
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderReadBits restBits
  let bw14 := BitWriter.writeBits bw bitsTot 14
  dynamicTablesAfterHeaderReaderAt bw14 restBits restLen
    (bitPos_lt_8_writeBits bw bitsTot 14 hbit)

set_option maxRecDepth 200000 in
/-- Rewrites the left transport prefix writer into the cached 44-bit prefix writer form. -/
lemma dynamicTablesAfterHeaderPrefix_eq_dynamicTables44PrefixWriter
    (bw : BitWriter) (restBits : Nat) :
    BitWriter.writeBits (dynamicTablesAfterHeaderBw30 bw restBits)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) =
      dynamicTables44PrefixWriter bw restBits := by
  simpa [dynamicTables44PrefixWriter] using
    congrArg
      (fun w =>
        BitWriter.writeBits w (dynamicHeaderCodeLenSymsRestBits restBits)
          (2 * dynamicHeaderCodeLenSyms.length))
      (dynamicTablesAfterHeader_bw30_eq_bw44 (bw := bw) (restBits := restBits))

set_option maxRecDepth 200000 in
/-- Rewrites the left transport full writer into the cached full-writer form. -/
lemma dynamicTablesAfterHeaderFull_eq_dynamicTablesAfterHeaderBwFull
    (bw : BitWriter) (restBits restLen : Nat) :
    BitWriter.writeBits (dynamicTablesAfterHeaderBw30 bw restBits)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (dynamicHeaderCodeLenSymsRestLen restLen) =
      dynamicTablesAfterHeaderBwFull bw restBits restLen := by
  calc
    BitWriter.writeBits (dynamicTablesAfterHeaderBw30 bw restBits)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (dynamicHeaderCodeLenSymsRestLen restLen) =
      dynamicTables44FullWriter bw restBits restLen := by
        simpa [dynamicTables44FullWriter] using
          congrArg
            (fun w =>
              BitWriter.writeBits w (dynamicHeaderCodeLenSymsRestBits restBits)
                (dynamicHeaderCodeLenSymsRestLen restLen))
            (dynamicTablesAfterHeader_bw30_eq_bw44 (bw := bw) (restBits := restBits))
    _ = dynamicTablesAfterHeaderBwFull bw restBits restLen := by
        exact dynamicTablesAfterHeader_bw44_full_eq
          (bw := bw) (restBits := restBits) (restLen := restLen)

end Png

end Bitmaps
