import Bitmap.Lemmas.Png.EncodeDecodeBase
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesHeaderReads
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesWriteBitsEq
import Bitmap.Lemmas.Png.DynamicBlockProofsConcreteHeader

namespace Bitmaps

namespace Lemmas

open Png

set_option maxRecDepth 200000 in
/-- Exposes the first three block-header bits of the dynamic stream as one writer/readback step. -/
lemma dynamicHeaderRead_writeBits_prefix
    (bw : BitWriter) (restBits : Nat) :
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) dynamicHeaderTableLen =
      BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen := by
  have htableLt : dynamicHeaderTableBits < 2 ^ dynamicHeaderTableLen := by
    exact dynamicHeaderTableBits_lt_pow
  have hmod :
      dynamicHeaderReadBits restBits % 2 ^ dynamicHeaderTableLen = dynamicHeaderTableBits := by
    rw [dynamicHeaderReadBits_eq_table_append]
    calc
      (dynamicHeaderTableBits ||| (restBits <<< dynamicHeaderTableLen)) % 2 ^ dynamicHeaderTableLen
          = dynamicHeaderTableBits % 2 ^ dynamicHeaderTableLen := by
              simpa using
                (mod_two_pow_or_shift
                  (a := dynamicHeaderTableBits) (b := restBits)
                  (k := dynamicHeaderTableLen) (len := dynamicHeaderTableLen) (by decide))
      _ = dynamicHeaderTableBits := Nat.mod_eq_of_lt htableLt
  calc
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) dynamicHeaderTableLen =
        BitWriter.writeBits bw
          (dynamicHeaderReadBits restBits % 2 ^ dynamicHeaderTableLen)
          dynamicHeaderTableLen := by
            simpa using (writeBits_mod bw (dynamicHeaderReadBits restBits) dynamicHeaderTableLen)
    _ = BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen := by
          rw [hmod]

set_option maxRecDepth 200000 in
/-- Rewrites the dynamic block header into the exact `readBits 3` payload consumed by the decoder. -/
lemma dynamicHeaderRead_writeBits_eq
    (bw : BitWriter) (restBits restLen : Nat) :
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) (dynamicHeaderReadLen restLen) =
      BitWriter.writeBits
        (BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen)
        restBits restLen := by
  have htableLt : dynamicHeaderTableBits < 2 ^ dynamicHeaderTableLen := by
    exact dynamicHeaderTableBits_lt_pow
  have hlen : dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
    simpa using dynamicHeaderReadLen_eq restLen
  calc
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) (dynamicHeaderReadLen restLen) =
      BitWriter.writeBits bw
        (dynamicHeaderTableBits ||| (restBits <<< dynamicHeaderTableLen))
        (dynamicHeaderTableLen + restLen) := by
          rw [dynamicHeaderReadBits_eq_table_append, hlen]
    _ =
      BitWriter.writeBits
        (BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen)
        restBits restLen := by
          simpa using
            (writeBits_concat bw dynamicHeaderTableBits restBits
              dynamicHeaderTableLen restLen htableLt)

set_option maxRecDepth 200000 in
/-- Collapses the dynamic encoder output into a single stream writer used by the loop proof. -/
lemma deflateDynamicFast_eq_streamWriter (raw : ByteArray) :
    let payloadBits := fixedLitBitsEob raw.data 0
    let hdr0 := BitWriter.empty
    let hdrHeader := BitWriter.writeBits hdr0 5 3
    let streamBits := dynamicHeaderReadBits payloadBits.1
    let streamLen := dynamicHeaderReadLen payloadBits.2
    deflateDynamicFast raw = (BitWriter.writeBits hdrHeader streamBits streamLen).flush := by
  let payloadBits := fixedLitBitsEob raw.data 0
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let streamBits := dynamicHeaderReadBits payloadBits.1
  let streamLen := dynamicHeaderReadLen payloadBits.2
  have hbits :
      5 ||| (dynamicHeaderTableBits <<< 3) ||| (payloadBits.1 <<< (3 + dynamicHeaderTableLen)) =
        5 ||| (streamBits <<< 3) := by
    dsimp [streamBits]
    rw [dynamicHeaderReadBits_eq_table_append]
    simp [Nat.or_assoc, Nat.shiftLeft_or_distrib, shiftLeft_shiftLeft, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]
  have hlen :
      3 + dynamicHeaderTableLen + payloadBits.2 = 3 + streamLen := by
    dsimp [streamLen]
    rw [dynamicHeaderReadLen_eq]
    omega
  have hprefixLt : 5 < 2 ^ 3 := by
    decide
  have hconcat :
      BitWriter.writeBits hdr0 (5 ||| (streamBits <<< 3)) (3 + streamLen) =
        BitWriter.writeBits hdrHeader streamBits streamLen := by
    simpa [hdr0, hdrHeader] using
      (writeBits_concat BitWriter.empty 5 streamBits 3 streamLen hprefixLt)
  calc
    deflateDynamicFast raw =
      (BitWriter.writeBits hdr0
        (5 ||| (dynamicHeaderTableBits <<< 3) ||| (payloadBits.1 <<< (3 + dynamicHeaderTableLen)))
        (3 + dynamicHeaderTableLen + payloadBits.2)).flush := by
          simpa [payloadBits, hdr0, hdrHeader, streamBits, streamLen] using
            deflateDynamicFast_eq_writeBits raw
    _ = (BitWriter.writeBits hdr0 (5 ||| (streamBits <<< 3)) (3 + streamLen)).flush := by
          rw [hbits, hlen]
    _ = (BitWriter.writeBits hdrHeader streamBits streamLen).flush := by
          simpa using congrArg BitWriter.flush hconcat

set_option maxRecDepth 200000 in
/-- Identifies the reader after the table section with the reader at the payload start. -/
lemma dynamicTablesReaderAt_eq_payloadReader
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) :
    dynamicTablesReaderAt bw restBits restLen hbit =
      BitWriter.readerAt
        (BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen)
        (BitWriter.writeBits
          (BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen)
          restBits restLen).flush
        (flush_size_writeBits_le
          (BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen)
          restBits restLen)
        (bitPos_lt_8_writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen hbit) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw14 := BitWriter.writeBits bw bitsTot dynamicHeaderTableLen
  let bwPayload :=
    BitWriter.writeBits
      (BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen)
      restBits restLen
  have hprefix :
      bw14 = BitWriter.writeBits bw dynamicHeaderTableBits dynamicHeaderTableLen := by
    simpa [bw14] using dynamicHeaderRead_writeBits_prefix (bw := bw) (restBits := restBits)
  have hfull : bw' = bwPayload := by
    simpa [bw', bwPayload, lenTot] using
      dynamicHeaderRead_writeBits_eq (bw := bw) (restBits := restBits) (restLen := restLen)
  apply BitReader.ext <;>
    simp [dynamicTablesReaderAt, bitsTot, lenTot, bw', bw14, bwPayload, hprefix, hfull]

set_option maxRecDepth 200000 in
/-- Splits the full dynamic writer into a header-and-tables prefix followed by the fixed payload writer. -/
lemma deflateDynamicFast_eq_payloadWriter (raw : ByteArray) :
    let payloadBits := fixedLitBitsEob raw.data 0
    let hdr0 := BitWriter.empty
    let hdrHeader := BitWriter.writeBits hdr0 5 3
    let bwTables := BitWriter.writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
    deflateDynamicFast raw = (BitWriter.writeBits bwTables payloadBits.1 payloadBits.2).flush := by
  let payloadBits := fixedLitBitsEob raw.data 0
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let bwTables := BitWriter.writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
  have hwrite :
      BitWriter.writeBits hdrHeader (dynamicHeaderReadBits payloadBits.1)
        (dynamicHeaderReadLen payloadBits.2) =
        BitWriter.writeBits bwTables payloadBits.1 payloadBits.2 := by
    simpa [bwTables] using
      dynamicHeaderRead_writeBits_eq
        (bw := hdrHeader) (restBits := payloadBits.1) (restLen := payloadBits.2)
  calc
    deflateDynamicFast raw =
        (BitWriter.writeBits hdrHeader (dynamicHeaderReadBits payloadBits.1)
          (dynamicHeaderReadLen payloadBits.2)).flush := by
            simpa [payloadBits, hdr0, hdrHeader] using deflateDynamicFast_eq_streamWriter raw
    _ = (BitWriter.writeBits bwTables payloadBits.1 payloadBits.2).flush := by
          simpa using congrArg BitWriter.flush hwrite

end Lemmas

end Bitmaps
