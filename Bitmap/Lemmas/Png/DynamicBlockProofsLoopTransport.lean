import Bitmap.Lemmas.Png.EncodeDecodeBase
import Bitmap.Lemmas.Png.DynamicBlockProofsTables
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesHeaderReads
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesWriteBitsEq

namespace Bitmaps

namespace Lemmas

open Png

private def dynamicTablesAfterHeaderReaderLocal
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderReadBits restBits
  let bw14 := BitWriter.writeBits bw bitsTot 14
  dynamicTablesAfterHeaderReaderAt bw14 restBits restLen
    (bitPos_lt_8_writeBits bw bitsTot 14 hbit)

private def dynamicTablesReaderLocal
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  dynamicTablesReaderAt bw restBits restLen hbit

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Provides a local reader transport so the loop proof does not re-import the heavier global chain. -/
lemma dynamicTablesAfterHeaderReaderAt_eq_dynamicTablesReaderAt_local
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
    dynamicTablesAfterHeaderReaderLocal bw restBits restLen hbit =
      dynamicTablesReaderLocal bw restBits restLen hbit := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw14 := BitWriter.writeBits bw bitsTot 14
  let bw44 := BitWriter.writeBits bw bitsTot 44
  have hskip : 14 + 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
    have hsub : lenTot - (14 + 3 * dynamicHeaderCodeLenLens.length) =
        dynamicHeaderCodeLenSymsRestLen restLen := by
      simpa [lenTot] using dynamicHeaderReadLen_sub44 restLen
    omega
  have hk : 2 * dynamicHeaderCodeLenSyms.length ≤ lenTot - (14 + 3 * dynamicHeaderCodeLenLens.length) := by
    simpa [lenTot] using dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms restLen
  have hbit44 : bw44.bitPos < 8 := by
    simpa [bw44] using bitPos_lt_8_writeBits bw bitsTot 44 hbit
  have hafter684 :
      BitWriter.readerAt
          (BitWriter.writeBits bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
            (2 * dynamicHeaderCodeLenSyms.length))
          bw'.flush
          (by
            have hk : 2 * dynamicHeaderCodeLenSyms.length ≤ dynamicHeaderCodeLenSymsRestLen restLen := by
              simpa using dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms restLen
            simpa using
              (flush_size_writeBits_prefix bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
                (2 * dynamicHeaderCodeLenSyms.length) (dynamicHeaderCodeLenSymsRestLen restLen) hk))
          (bitPos_lt_8_writeBits bw44 (dynamicHeaderCodeLenSymsRestBits restBits)
            (2 * dynamicHeaderCodeLenSyms.length) hbit44) =
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot dynamicHeaderTableLen)
          bw'.flush
          (by
            have hk : dynamicHeaderTableLen ≤ lenTot := by
              simpa [lenTot] using dynamicHeaderTableLen_le_readLen restLen
            simpa [bw', lenTot] using
              (flush_size_writeBits_prefix bw bitsTot dynamicHeaderTableLen lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot dynamicHeaderTableLen hbit) := by
    simpa [bw44, bitsTot, lenTot, dynamicHeaderReadBits_shift44, dynamicHeaderTableLen_eq_split, bw']
      using
        (readerAt_writeBits_split_eq
          (bw := bw) (bits := bitsTot) (len := lenTot)
          (skip := 14 + 3 * dynamicHeaderCodeLenLens.length)
          (k := 2 * dynamicHeaderCodeLenSyms.length)
          hskip hk hbit)
  simpa [dynamicTablesAfterHeaderReaderLocal, dynamicTablesReaderLocal,
    dynamicTablesAfterHeaderReaderAt, dynamicTablesReaderAt, dynamicCodeLenSymsReaderAt,
    bitsTot, lenTot, bw', bw14, bw44]
    using hafter684

end Lemmas

end Bitmaps
