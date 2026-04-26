import Bitmap.Lemmas.Png.DynamicBlockProofsLoop
import Bitmap.Lemmas.Png.DynamicBlockProofsSpec
import Bitmap.Lemmas.Png.DynamicBlockProofsSpecConcrete
import Bitmap.Lemmas.Png.EncodeDecodeBase
import Bitmap.Lemmas.Png.EncodeDecodeBaseU32

namespace Bitmaps

namespace Lemmas

open U32Helpers
open Png
attribute [local simp] Png.byteArray_get_proof_irrel

/-- The concrete zlib byte stream that wraps `deflateDynamicFast`. -/
def zlibDynamicFastBytes (raw : ByteArray) : ByteArray :=
  ByteArray.mk #[u8 0x78, u8 0x01] ++ deflateDynamicFast raw ++ u32be (adler32 raw).toNat

/-- Dynamic zlib output uses the same fixed CMF/FLG envelope as the other encoders.
This wrapper keeps older dynamic proofs phrased in terms of `zlibCompressDynamic`. -/
lemma zlibCompressDynamic_cmf_flg (raw : ByteArray) :
    let bytes := zlibCompressDynamic raw
    let h0 : 0 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 0 < 6) (zlibCompressOf_size_ge (deflateDynamic raw) raw)
    let h1 : 1 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 1 < 6) (zlibCompressOf_size_ge (deflateDynamic raw) raw)
    bytes[0]'h0 = u8 0x78 ∧ bytes[1]'h1 = u8 0x01 := by
  simpa [zlibCompressDynamic_eq] using zlibCompressOf_cmf_flg (deflateDynamic raw) raw

/-- Extracting the zlib payload window from dynamic output returns the deflate stream.
This is the dynamic specialization of the generic zlib envelope lemma. -/
lemma zlibCompressDynamic_extract_deflated (raw : ByteArray) :
    (zlibCompressDynamic raw).extract 2 ((zlibCompressDynamic raw).size - 4) =
      deflateDynamic raw := by
  simpa [zlibCompressDynamic_eq] using
    zlibCompressOf_extract_deflated (deflateDynamic raw) raw

set_option maxRecDepth 400000 in
set_option maxHeartbeats 20000000 in
/-- Proves the real dynamic fast stream round-trips through the zlib decoder without fallback. -/
lemma zlibDecompress_deflateDynamicFast (raw : ByteArray) :
    zlibDecompress (zlibDynamicFastBytes raw)
      (by
        have hheader : (ByteArray.mk #[u8 0x78, u8 0x01] : ByteArray).size = 2 := by decide
        have hadler : (u32be (adler32 raw).toNat).size = 4 := by
          simpa using (u32be_size (adler32 raw).toNat)
        have :
            6 ≤
              (ByteArray.mk #[u8 0x78, u8 0x01] : ByteArray).size +
                (deflateDynamicFast raw).size +
                (u32be (adler32 raw).toNat).size := by
          simp [hheader, hadler]
        have h6 : 6 ≤ (zlibDynamicFastBytes raw).size := by
          simpa [zlibDynamicFastBytes, ByteArray.size_append, hheader, hadler, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using this
        omega) = some raw := by
  classical
  let payloadBits := fixedLitBitsEob raw.data 0
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let bwTables := BitWriter.writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
  let streamWriter := BitWriter.writeBits bwTables payloadBits.1 payloadBits.2
  let streamBits := dynamicHeaderReadBits payloadBits.1
  let streamLen := dynamicHeaderReadLen payloadBits.2
  let streamBitsFull := 5 ||| (streamBits <<< 3)
  let streamLenFull := 3 + streamLen
  let collapsedWriter := BitWriter.writeBits hdr0 streamBitsFull streamLenFull
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated : ByteArray := streamWriter.flush
  let adlerBytes : ByteArray := u32be (adler32 raw).toNat
  let bytes := zlibDynamicFastBytes raw
  have hheader : header.size = 2 := by decide
  have hadlerSize : adlerBytes.size = 4 := by
    simpa [adlerBytes] using (u32be_size (adler32 raw).toNat)
  have hfastPayload : deflateDynamicFast raw = deflated := by
    simpa [deflated, payloadBits, hdr0, hdrHeader, bwTables, streamWriter] using
      deflateDynamicFast_eq_payloadWriter raw
  have hbytes : bytes = header ++ deflated ++ adlerBytes := by
    simpa [bytes, zlibDynamicFastBytes, header, adlerBytes, ByteArray.append_assoc] using
      congrArg (fun x => header ++ x ++ adlerBytes) hfastPayload
  have hmin : 6 ≤ bytes.size := by
    have : 6 ≤ header.size + deflated.size + adlerBytes.size := by
      simp [hheader, hadlerSize, deflated]
    simpa [hbytes, ByteArray.size_append, hheader, hadlerSize,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hstream :
      collapsedWriter = BitWriter.writeBits hdrHeader streamBits streamLen := by
    have hbits : 5 < 2 ^ 3 := by decide
    simpa [collapsedWriter, hdrHeader, streamBitsFull, streamLenFull] using
      (writeBits_concat hdr0 5 streamBits 3 streamLen hbits)
  have hpayloadData :
      streamWriter.flush = collapsedWriter.flush := by
    calc
      streamWriter.flush = deflateDynamicFast raw := by
        symm
        simpa [payloadBits, hdr0, hdrHeader, bwTables, streamWriter] using
          deflateDynamicFast_eq_payloadWriter raw
      _ = (BitWriter.writeBits hdrHeader streamBits streamLen).flush := by
        simpa [payloadBits, hdr0, hdrHeader, streamBits, streamLen] using
          deflateDynamicFast_eq_streamWriter raw
      _ = collapsedWriter.flush := by
        simp [hstream]
  have hbitHeader : hdrHeader.bitPos < 8 := by
    simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
  have hbitTables : bwTables.bitPos < 8 := by
    simpa [bwTables] using
      bitPos_lt_8_writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen hbitHeader
  let streamReader0 : BitReader := {
    data := collapsedWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  let streamReaderFinal := BitWriter.readerAt streamWriter streamWriter.flush (by rfl)
    (bitPos_lt_8_writeBits bwTables payloadBits.1 payloadBits.2 hbitTables)
  have hloop :
      zlibDecompressLoop streamReader0 ByteArray.empty = some (streamReaderFinal, raw) := by
    simpa [payloadBits, hdr0, hdrHeader, bwTables, streamWriter, streamBits, streamLen,
      streamBitsFull, streamLenFull, collapsedWriter, streamReader0, streamReaderFinal] using
      zlibDecompressLoop_deflateDynamicFast_stream raw
  have h0 : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1 : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have h0' : 0 < bytes.size := h0
  have h1' : 1 < bytes.size := h1
  have h0h : 0 < header.size := by simp [hheader]
  have h1h : 1 < header.size := by simp [hheader]
  have hheaderLe : header.size ≤ (header ++ deflated ++ adlerBytes).size := by
    simp [ByteArray.size_append]
    omega
  have h0Bytes : 0 < (header ++ deflated ++ adlerBytes).size := lt_of_lt_of_le h0h hheaderLe
  have h1Bytes : 1 < (header ++ deflated ++ adlerBytes).size := lt_of_lt_of_le h1h hheaderLe
  have hcmf' : bytes[0]'h0' = u8 0x78 := by
    have hget0 :
        (header ++ deflated ++ adlerBytes)[0]'h0Bytes = header[0]'h0h := by
      have hget :=
        ByteArray.get_append_left (a := header) (b := deflated ++ adlerBytes) (i := 0) h0h
      simpa [ByteArray.append_assoc] using hget
    have hheader0 : header[0]'h0h = u8 0x78 := by
      rfl
    simpa [hbytes, header, ByteArray.append_assoc] using hget0.trans hheader0
  have hflg' : bytes[1]'h1' = u8 0x01 := by
    have hget1 :
        (header ++ deflated ++ adlerBytes)[1]'h1Bytes = header[1]'h1h := by
      have hget :=
        ByteArray.get_append_left (a := header) (b := deflated ++ adlerBytes) (i := 1) h1h
      simpa [ByteArray.append_assoc] using hget
    have hheader1 : header[1]'h1h = u8 0x01 := by
      rfl
    simpa [hbytes, header, ByteArray.append_assoc] using hget1.trans hheader1
  have hcmf : bytes.get 0 h0 = u8 0x78 := by
    have htmp : bytes.get 0 h0' = u8 0x78 := by
      simpa [byteArray_get_eq_getElem] using hcmf'
    simpa using htmp
  have hflg : bytes.get 1 h1 = u8 0x01 := by
    have htmp : bytes.get 1 h1' = u8 0x01 := by
      simpa [byteArray_get_eq_getElem] using hflg'
    simpa using htmp
  have hsize'' : header.size + deflated.size + adlerBytes.size - 4 = deflated.size + 2 := by
    simp [hheader, hadlerSize]
    omega
  have hdeflated : bytes.extract 2 (bytes.size - 4) = streamWriter.flush := by
    calc
      bytes.extract 2 (bytes.size - 4)
          = (header ++ deflated ++ adlerBytes).extract 2
              (header.size + deflated.size + adlerBytes.size - 4) := by
                simp [hbytes, ByteArray.size_append, hheader, hadlerSize]
      _ = (header ++ deflated ++ adlerBytes).extract 2 (deflated.size + 2) := by
            simp [hsize'']
      _ = (deflated ++ adlerBytes).extract 0 deflated.size := by
            have h :=
              (ByteArray.extract_append_size_add
                (a := header) (b := deflated ++ adlerBytes) (i := 0) (j := deflated.size))
            simpa [hheader, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using h
      _ = deflated := by
            have hprefix :
                (deflated ++ adlerBytes).extract 0 deflated.size = deflated.extract 0 deflated.size := by
              exact
                byteArray_extract_append_prefix
                  (a := deflated) (b := adlerBytes) (n := deflated.size) (by exact le_rfl)
            simp [hprefix, ByteArray.extract_zero_size]
      _ = streamWriter.flush := rfl
  have hAdlerPos : bytes.size - 4 + 3 < bytes.size := by
    omega
  have hadler : readU32BE bytes (bytes.size - 4) hAdlerPos = (adler32 raw).toNat := by
    have hextract :
        bytes.extract (bytes.size - 4) (bytes.size - 4 + 4) =
          adlerBytes := by
      have hprefix : (header ++ deflated).size = deflated.size + 2 := by
        simp [ByteArray.size_append, hheader, Nat.add_comm]
      calc
        bytes.extract (bytes.size - 4) (bytes.size - 4 + 4)
            = (header ++ deflated ++ adlerBytes).extract
                (header.size + deflated.size + adlerBytes.size - 4)
                (header.size + deflated.size + adlerBytes.size - 4 + 4) := by
                  simp [hbytes, ByteArray.size_append, hheader, hadlerSize]
        _ = (header ++ deflated ++ adlerBytes).extract (deflated.size + 2) (deflated.size + 2 + 4) := by
              simp [hsize'']
        _ = adlerBytes.extract 0 adlerBytes.size := by
              have h :=
                (ByteArray.extract_append_size_add
                  (a := header ++ deflated) (b := adlerBytes) (i := 0) (j := adlerBytes.size))
              simpa [hprefix, hadlerSize, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using h
        _ = adlerBytes := by
              simp [ByteArray.extract_zero_size]
    have hlt : (adler32 raw).toNat < 2 ^ 32 := by
      simpa using (UInt32.toNat_lt (adler32 raw))
    exact readU32BE_of_extract_eq (bytes := bytes) (pos := bytes.size - 4)
      (n := (adler32 raw).toNat) (h := hAdlerPos) (by simpa [adlerBytes] using hextract) hlt
  have hmod : ((u8 0x78).toNat <<< 8 + (u8 0x01).toNat) % 31 = 0 := by
    decide
  have hbtype : (u8 0x78 &&& (0x0F : UInt8)) = 8 := by
    decide
  have hflg0 : (u8 0x01 &&& (0x20 : UInt8)) = 0 := by
    decide
  have hsizeZ : 2 ≤ bytes.size := by
    omega
  change zlibDecompress bytes hsizeZ = some raw
  unfold zlibDecompress
  simp [bytes, hcmf, hflg, hmod, hbtype, hflg0, hdeflated, hpayloadData]
  rw [hloop]
  have hAlign : streamReaderFinal.alignByte.bytePos = streamWriter.flush.size := by
    simpa [streamReaderFinal] using
      (readerAt_alignByte_bytePos_eq_flush
        (bw := streamWriter)
        (hbit := bitPos_lt_8_writeBits bwTables payloadBits.1 payloadBits.2 hbitTables))
  have hsize : bytes.size = streamWriter.flush.size + 6 := by
    simp [hbytes, ByteArray.size_append, hheader, hadlerSize, deflated,
      Nat.add_left_comm, Nat.add_comm]
    omega
  have hposEq : streamReaderFinal.alignByte.bytePos + 2 = bytes.size - 4 := by
    have : streamWriter.flush.size + 2 = (streamWriter.flush.size + 6) - 4 := by omega
    simpa [hAlign, hsize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hAdlerPos' : streamReaderFinal.alignByte.bytePos + 2 + 3 < bytes.size := by
    simpa [hposEq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAdlerPos
  have hread :
      readU32BE bytes (streamReaderFinal.alignByte.bytePos + 2) hAdlerPos' = (adler32 raw).toNat := by
    simpa [hposEq, readU32BE_proof_irrel] using hadler
  simp [hAdlerPos', hread, bytes]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- The real dynamic deflate stream starts with a non-stored block header, so
the stored-only inflater rejects it immediately. -/
lemma inflateStored_deflateDynamicFast_none (raw : ByteArray) :
    inflateStored (deflateDynamicFast raw) = none := by
  let payloadBits := fixedLitBitsEob raw.data 0
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let streamBits := dynamicHeaderReadBits payloadBits.1
  let streamLen := dynamicHeaderReadLen payloadBits.2
  let streamBitsFull := 5 ||| (streamBits <<< 3)
  let streamLenFull := 3 + streamLen
  let collapsedWriter := BitWriter.writeBits hdr0 streamBitsFull streamLenFull
  let streamReader0 : BitReader := {
    data := collapsedWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  have hstream :
      collapsedWriter = BitWriter.writeBits hdrHeader streamBits streamLen := by
    have hbits : 5 < 2 ^ 3 := by decide
    simpa [collapsedWriter, hdrHeader, streamBitsFull, streamLenFull] using
      (writeBits_concat hdr0 5 streamBits 3 streamLen hbits)
  have hdata :
      deflateDynamicFast raw = collapsedWriter.flush := by
    calc
      deflateDynamicFast raw = (BitWriter.writeBits hdrHeader streamBits streamLen).flush := by
        simpa [payloadBits, hdr0, hdrHeader, streamBits, streamLen] using
          deflateDynamicFast_eq_streamWriter raw
      _ = collapsedWriter.flush := by
        exact congrArg BitWriter.flush hstream.symm
  have hread0 : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [streamReader0, BitWriter.readerAt, hdr0, BitWriter.empty] using
      (readerAt_writeBits_bound (bw := hdr0) (bits := streamBitsFull) (len := streamLenFull)
        (k := 3) (hk := by omega) (hbit := by decide))
  have hread :
      streamReader0.readBits 3 hread0 =
        (5,
          BitWriter.readerAt hdrHeader
            (BitWriter.writeBits hdrHeader streamBits streamLen).flush
            (flush_size_writeBits_le hdrHeader streamBits streamLen)
            (by
              simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide))) := by
    simpa [payloadBits, hdr0, hdrHeader, streamBits, streamLen, streamBitsFull, streamLenFull,
      collapsedWriter, streamReader0] using dynamicStreamReader0_readBits3 raw
  have hreadAux :
      streamReader0.readBits 3 hread0 = streamReader0.readBitsAux 3 := by
    simpa [BitReader.readBits] using
      (readBitsFastU32_eq_readBitsAux (br := streamReader0) (n := 3) (h := hread0))
  have hpos : 0 < collapsedWriter.flush.size := by
    have : 3 ≤ collapsedWriter.flush.size * 8 := by
      simpa [streamReader0] using hread0
    by_contra hzero
    have hsize0 : collapsedWriter.flush.size = 0 := Nat.eq_zero_of_not_pos hzero
    omega
  have haux :
      streamReader0.readBitsAux 3 =
        (((collapsedWriter.flush.get 0 hpos).toNat >>> 0) % 2 ^ 3,
          { data := collapsedWriter.flush
            bytePos := 0
            bitPos := 3
            hpos := by exact Nat.zero_le _
            hend := by
              intro hEq
              have : False := by
                simp [hEq] at hpos
              exact False.elim this
            hbit := by decide }) := by
    simpa [streamReader0] using
      (readBitsAux_within_byte_lt (br := streamReader0) (n := 3)
        (hspan := by simp [streamReader0]) (hlt := hpos))
  have hmod :
      ((collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3) = 5 := by
    have hreadFst : (streamReader0.readBits 3 hread0).1 = 5 := by
      simpa using congrArg Prod.fst hread
    have hauxFst :
        (streamReader0.readBitsAux 3).1 =
          ((collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3) := by
      simpa using congrArg Prod.fst haux
    calc
      (collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3 =
          (streamReader0.readBitsAux 3).1 := hauxFst.symm
      _ = (streamReader0.readBits 3 hread0).1 := by
        simp [hreadAux]
      _ = 5 := hreadFst
  have hbit2mod : (((collapsedWriter.flush.get 0 hpos).toNat % 2 ^ 3).testBit 2) = true := by
    rw [hmod]
    decide
  have hbit2 : ((collapsedWriter.flush.get 0 hpos).toNat).testBit 2 = true := by
    have hbit2mod' := hbit2mod
    rw [Nat.testBit_mod_two_pow] at hbit2mod'
    simpa using hbit2mod'
  let header := collapsedWriter.flush.get 0 hpos
  have hmaskedBit : (((header.toNat >>> 1) &&& 3).testBit 1) = true := by
    simp [header, hbit2, Nat.testBit_shiftRight]
    decide
  have hbtypeNat : ((header.toNat >>> 1) &&& 3) ≠ 0 := by
    intro hzero
    have : (((header.toNat >>> 1) &&& 3).testBit 1) = false := by
      simp [hzero]
    rw [hmaskedBit] at this
    cases this
  have hbtype : ((header >>> 1) &&& (0x03 : UInt8)) ≠ 0 := by
    intro h0
    have h0' : (header.toNat >>> 1) &&& 3 = 0 := by
      have h0' := congrArg UInt8.toNat h0
      simpa [UInt8.toNat_and, UInt8.toNat_shiftRight] using h0'
    exact hbtypeNat h0'
  have hauxNone : inflateStoredAux collapsedWriter.flush hpos = none := by
    unfold inflateStoredAux
    simp [header, hbtype]
  have hstored : inflateStored collapsedWriter.flush = none := by
    simp [inflateStored, hpos, hauxNone]
  simpa [hdata] using hstored

/-- Stored-only zlib decompression rejects real dynamic-compression streams. -/
lemma zlibDecompressStored_zlibCompressDynamic_none (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressDynamic raw).size) :
    zlibDecompressStored (zlibCompressDynamic raw) hsize = none := by
  let bytes := zlibCompressDynamic raw
  have hmin : 6 ≤ bytes.size := zlibCompressDynamic_size_ge raw
  have h0 : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1 : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have h0' : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1' : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have hcmf' : bytes[0]'h0' = u8 0x78 := (zlibCompressDynamic_cmf_flg raw).1
  have hflg' : bytes[1]'h1' = u8 0x01 := (zlibCompressDynamic_cmf_flg raw).2
  have hcmf : bytes.get 0 h0 = u8 0x78 := by
    have htmp : bytes.get 0 h0' = u8 0x78 := by
      simpa [byteArray_get_eq_getElem] using hcmf'
    simpa using htmp
  have hflg : bytes.get 1 h1 = u8 0x01 := by
    have htmp : bytes.get 1 h1' = u8 0x01 := by
      simpa [byteArray_get_eq_getElem] using hflg'
    simpa using htmp
  have hdeflated : bytes.extract 2 (bytes.size - 4) = deflateDynamic raw := by
    simpa [bytes] using zlibCompressDynamic_extract_deflated raw
  have hinflate : inflateStored (bytes.extract 2 (bytes.size - 4)) = none := by
    simpa [hdeflated, deflateDynamic] using inflateStored_deflateDynamicFast_none raw
  have hmod : ((u8 0x78).toNat <<< 8 + (u8 0x01).toNat) % 31 = 0 := by
    decide
  have hbtype : (u8 0x78 &&& (0x0F : UInt8)) = 8 := by
    decide
  have hflg0 : (u8 0x01 &&& (0x20 : UInt8)) = 0 := by
    decide
  unfold zlibDecompressStored
  simp [bytes, hcmf, hflg, hmin, hinflate, hmod, hbtype, hflg0]

/-- Zlib decompression of real dynamic-compression output yields the original bytes. -/
lemma zlibDecompress_zlibCompressDynamic (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressDynamic raw).size) :
    zlibDecompress (zlibCompressDynamic raw) hsize = some raw := by
  simpa [zlibCompressDynamic, zlibDynamicFastBytes, deflateDynamic, ByteArray.append_assoc] using
    zlibDecompress_deflateDynamicFast raw

end Lemmas

end Bitmaps
