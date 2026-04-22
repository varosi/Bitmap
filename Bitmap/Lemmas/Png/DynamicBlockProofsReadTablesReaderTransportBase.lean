import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesWriteBitsEq

namespace Bitmaps

namespace Png

def dynamicTablesAfterHeaderBw30 (bw : BitWriter) (restBits : Nat) : BitWriter :=
  let bitsTot := dynamicHeaderReadBits restBits
  let bw14 := BitWriter.writeBits bw bitsTot 14
  BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits)
    (3 * dynamicHeaderCodeLenLens.length)

def dynamicTablesAfterHeaderBw44 (bw : BitWriter) (restBits : Nat) : BitWriter :=
  BitWriter.writeBits bw (dynamicHeaderReadBits restBits) 44

def dynamicTablesAfterHeaderBwFull
    (bw : BitWriter) (restBits restLen : Nat) : BitWriter :=
  BitWriter.writeBits bw (dynamicHeaderReadBits restBits) (dynamicHeaderReadLen restLen)

def dynamicTables44PrefixWriter
    (bw : BitWriter) (restBits : Nat) : BitWriter :=
  BitWriter.writeBits (dynamicTablesAfterHeaderBw44 bw restBits)
    (dynamicHeaderCodeLenSymsRestBits restBits)
    (2 * dynamicHeaderCodeLenSyms.length)

def dynamicTables44FullWriter
    (bw : BitWriter) (restBits restLen : Nat) : BitWriter :=
  BitWriter.writeBits (dynamicTablesAfterHeaderBw44 bw restBits)
    (dynamicHeaderCodeLenSymsRestBits restBits)
    (dynamicHeaderCodeLenSymsRestLen restLen)

set_option maxRecDepth 200000 in
/-- Relates the 30-bit and 44-bit writer splits used by the post-header transport proof. -/
lemma dynamicTablesAfterHeader_bw30_eq_bw44
    (bw : BitWriter) (restBits : Nat) :
    dynamicTablesAfterHeaderBw30 bw restBits =
      dynamicTablesAfterHeaderBw44 bw restBits := by
  unfold dynamicTablesAfterHeaderBw30 dynamicTablesAfterHeaderBw44
  let bitsTot := dynamicHeaderReadBits restBits
  calc
    BitWriter.writeBits (BitWriter.writeBits bw bitsTot 14)
        (dynamicHeaderCodeLenLensBits restBits)
        (3 * dynamicHeaderCodeLenLens.length) =
      BitWriter.writeBits (BitWriter.writeBits bw bitsTot 14)
        (bitsTot >>> 14)
        (3 * dynamicHeaderCodeLenLens.length) := by
          rw [dynamicHeaderReadBits_shift14]
    _ = BitWriter.writeBits bw bitsTot (14 + 3 * dynamicHeaderCodeLenLens.length) := by
          symm
          simpa using
            (writeBits_split bw bitsTot 14 (3 * dynamicHeaderCodeLenLens.length))
    _ = BitWriter.writeBits bw bitsTot 44 := by
          have h44 : 14 + 3 * dynamicHeaderCodeLenLens.length = 44 := by
            native_decide
          simp [h44]

set_option maxRecDepth 200000 in
/-- Extends the 44-bit split to the full writer that also contains the remaining payload bits. -/
lemma dynamicTablesAfterHeader_bw44_full_eq
    (bw : BitWriter) (restBits restLen : Nat) :
    dynamicTables44FullWriter bw restBits restLen =
      dynamicTablesAfterHeaderBwFull bw restBits restLen := by
  unfold dynamicTables44FullWriter dynamicTablesAfterHeaderBw44 dynamicTablesAfterHeaderBwFull
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  calc
    BitWriter.writeBits (BitWriter.writeBits bw bitsTot 44)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (dynamicHeaderCodeLenSymsRestLen restLen) =
      BitWriter.writeBits (BitWriter.writeBits bw bitsTot 44)
        (bitsTot >>> 44) (lenTot - 44) := by
          have hsub : lenTot - 44 = dynamicHeaderCodeLenSymsRestLen restLen := by
            simpa [lenTot] using dynamicHeaderReadLen_sub44 restLen
          rw [show bitsTot >>> 44 = dynamicHeaderCodeLenSymsRestBits restBits by
            simpa [bitsTot] using dynamicHeaderReadBits_shift44 restBits]
          simp [hsub]
    _ = BitWriter.writeBits bw bitsTot (44 + (lenTot - 44)) := by
          symm
          simpa using (writeBits_split bw bitsTot 44 (lenTot - 44))
    _ = BitWriter.writeBits bw bitsTot lenTot := by
          have hk : 44 ≤ lenTot := by
            have h44 : 44 ≤ dynamicHeaderTableLen := by
              native_decide
            have htab : dynamicHeaderTableLen ≤ lenTot := by
              simpa [lenTot] using dynamicHeaderTableLen_le_readLen restLen
            omega
          simp [Nat.add_sub_of_le hk]

/-- Records that the two equivalent full writers flush to the same byte array. -/
lemma dynamicTablesAfterHeader_bw44_full_flush_eq
    (bw : BitWriter) (restBits restLen : Nat) :
    (dynamicTables44FullWriter bw restBits restLen).flush =
      (dynamicTablesAfterHeaderBwFull bw restBits restLen).flush := by
  simpa using congrArg BitWriter.flush
    (dynamicTablesAfterHeader_bw44_full_eq
      (bw := bw) (restBits := restBits) (restLen := restLen))

set_option maxRecDepth 200000 in
/-- Supplies the flush-size bound needed to build the intermediate 44-bit reader. -/
lemma dynamicTables44PrefixWriter_flush_le
    (bw : BitWriter) (restBits restLen : Nat) :
    (dynamicTables44PrefixWriter bw restBits).flush.size ≤
      (dynamicTablesAfterHeaderBwFull bw restBits restLen).flush.size := by
  have hk : 2 * dynamicHeaderCodeLenSyms.length ≤ dynamicHeaderCodeLenSymsRestLen restLen := by
    simpa using dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms restLen
  have hprefix :
      (dynamicTables44PrefixWriter bw restBits).flush.size ≤
        (dynamicTables44FullWriter bw restBits restLen).flush.size := by
    simpa [dynamicTables44PrefixWriter, dynamicTables44FullWriter] using
      (flush_size_writeBits_prefix (dynamicTablesAfterHeaderBw44 bw restBits)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length)
        (dynamicHeaderCodeLenSymsRestLen restLen) hk)
  have hflush :
      (dynamicTables44FullWriter bw restBits restLen).flush =
        (dynamicTablesAfterHeaderBwFull bw restBits restLen).flush := by
    simpa using
      (dynamicTablesAfterHeader_bw44_full_flush_eq
        (bw := bw) (restBits := restBits) (restLen := restLen))
  have hsize :
      (dynamicTables44FullWriter bw restBits restLen).flush.size =
        (dynamicTablesAfterHeaderBwFull bw restBits restLen).flush.size := by
    simpa using congrArg ByteArray.size hflush
  simpa [hsize] using hprefix

set_option maxRecDepth 200000 in
/-- Supplies the bit-position bound needed to build the intermediate 44-bit reader. -/
lemma dynamicTables44PrefixWriter_bitPos_lt
    (bw : BitWriter) (restBits : Nat) (hbit : bw.bitPos < 8) :
    (dynamicTables44PrefixWriter bw restBits).bitPos < 8 := by
  have hbit44 : (dynamicTablesAfterHeaderBw44 bw restBits).bitPos < 8 := by
    simpa [dynamicTablesAfterHeaderBw44] using
      bitPos_lt_8_writeBits bw (dynamicHeaderReadBits restBits) 44 hbit
  simpa [dynamicTables44PrefixWriter] using
    bitPos_lt_8_writeBits (dynamicTablesAfterHeaderBw44 bw restBits)
      (dynamicHeaderCodeLenSymsRestBits restBits)
      (2 * dynamicHeaderCodeLenSyms.length) hbit44

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
def dynamicTables44Reader
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt
    (dynamicTables44PrefixWriter bw restBits)
    (dynamicTablesAfterHeaderBwFull bw restBits restLen).flush
    (dynamicTables44PrefixWriter_flush_le bw restBits restLen)
    (dynamicTables44PrefixWriter_bitPos_lt bw restBits hbit)

set_option maxRecDepth 200000 in
/-- Identifies the explicit 44-bit reader with the abstract dynamic table reader state. -/
lemma writeBits44Reader_eq_dynamicTablesReaderAt
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
    dynamicTables44Reader bw restBits restLen hbit =
      dynamicTablesReaderAt bw restBits restLen hbit := by
  unfold dynamicTables44Reader dynamicTablesReaderAt
  apply readerAt_eq_of_eqs
  · simpa [dynamicTables44PrefixWriter, dynamicTablesAfterHeaderBw44] using
      (dynamicHeaderCodeLenSyms_writeBits_eq (bw := bw) (restBits := restBits)).symm
  · rfl

end Png

end Bitmaps
