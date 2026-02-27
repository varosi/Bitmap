import Bitmap.Lemmas.Png.EncodeDecodeBase
import Bitmap.Lemmas.Png.FixedBlockBase

universe u

namespace Bitmaps

namespace Lemmas

open Png
attribute [local simp] Png.byteArray_get_proof_irrel

set_option maxHeartbeats 6000000 in
-- Zlib decompression of fixed-compression output yields the original bytes.
lemma zlibDecompress_zlibCompressFixed (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressFixed raw).size) :
    zlibDecompress (zlibCompressFixed raw) hsize = some raw := by
  classical
  let bytes := zlibCompressFixed raw
  have hmin : 6 ≤ bytes.size := zlibCompressFixed_size_ge raw
  have h0 : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1 : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have h0' : 0 < bytes.size := h0
  have h1' : 1 < bytes.size := h1
  have hcmf' : bytes[0]'h0' = u8 0x78 := (zlibCompressFixed_cmf_flg raw).1
  have hflg' : bytes[1]'h1' = u8 0x01 := (zlibCompressFixed_cmf_flg raw).2
  have hcmf : bytes.get 0 h0 = u8 0x78 := by
    have htmp : bytes.get 0 h0' = u8 0x78 := by
      simpa [byteArray_get_eq_getElem] using hcmf'
    simpa using htmp
  have hflg : bytes.get 1 h1 = u8 0x01 := by
    have htmp : bytes.get 1 h1' = u8 0x01 := by
      simpa [byteArray_get_eq_getElem] using hflg'
    simpa using htmp
  have hdeflated : bytes.extract 2 (bytes.size - 4) = deflateFixed raw := by
    simpa [bytes] using zlibCompressFixed_extract_deflated raw
  have hAdlerPos : bytes.size - 4 + 3 < bytes.size := by omega
  have hadler : readU32BE bytes (bytes.size - 4) hAdlerPos = (adler32 raw).toNat := by
    have hextract :
        bytes.extract (bytes.size - 4) (bytes.size - 4 + 4) =
          u32be (adler32 raw).toNat := by
      simpa [bytes] using zlibCompressFixed_extract_adler raw
    have hlt : (adler32 raw).toNat < 2 ^ 32 := by
      simpa using (UInt32.toNat_lt (adler32 raw))
    exact readU32BE_of_extract_eq (bytes := bytes) (pos := bytes.size - 4)
      (n := (adler32 raw).toNat) (h := hAdlerPos) hextract hlt
  have hmod : ((u8 0x78).toNat <<< 8 + (u8 0x01).toNat) % 31 = 0 := by
    decide
  have hbtype : (u8 0x78 &&& (0x0F : UInt8)) = 8 := by
    decide
  have hflg0 : (u8 0x01 &&& (0x20 : UInt8)) = 0 := by
    decide
  -- prepare the fixed literal bitstream decoder
  let hdr0 := BitWriter.empty
  let hdrBfinal := hdr0.writeBits 1 1
  let hdrHeader := hdrBfinal.writeBits 1 2
  let payloadBits := fixedLitBitsEob raw.data 0
  have hdeflateBits :
      deflateFixed raw = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := by
    simpa using deflateFixed_eq_writeBits raw
  have hdecode :
      decodeFixedLiteralBlock
          (BitWriter.readerAt hdrHeader (deflateFixed raw)
            (by
              -- `hdrHeader` is a prefix of the deflated stream
              simpa [hdeflateBits] using
                (flush_size_writeBits_le (bw := hdrHeader) (bits := payloadBits.1) (len := payloadBits.2)))
            (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide))))
          ByteArray.empty =
        some (BitWriter.readerAt (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2) (deflateFixed raw)
          (by
            simp [hdeflateBits])
          (bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2
            (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide)))),
          raw) := by
    have hcur0 : hdr0.curClearAbove := curClearAbove_empty
    have hcur1 : hdrBfinal.curClearAbove := curClearAbove_writeBits hdr0 1 1 (by decide) hcur0
    have hcur2 : hdrHeader.curClearAbove := curClearAbove_writeBits hdrBfinal 1 2 (by decide) hcur1
    have hbits := decodeFixedLiteralBlock_fixedLitBitsEob (data := raw.data) (i := 0)
      (bw := hdrHeader) (out := ByteArray.empty)
      (hbit := bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide)))
      (hcur := hcur2)
    -- rewrite the output ByteArray
    have hraw : byteArrayFromArray raw.data 0 ByteArray.empty = raw := by
      simpa using byteArrayFromArray_empty (data := raw.data)
    simpa [payloadBits, hdeflateBits, hraw] using hbits
  -- Collapse the header bits into one write.
  let streamBits := 3 ||| (payloadBits.1 <<< 3)
  let streamLen := 3 + payloadBits.2
  let streamWriter := BitWriter.writeBits hdr0 streamBits streamLen
  have hbw2 : hdrHeader = BitWriter.writeBits hdr0 3 3 := by
    have hbits : (1 : Nat) < 2 ^ 1 := by decide
    have hconcat := writeBits_concat hdr0 1 1 1 2 hbits
    have h' : BitWriter.writeBits hdr0 3 3 = hdrHeader := by
      simpa [hdrBfinal, hdrHeader] using hconcat
    simpa using h'.symm
  have hdeflateTotal : deflateFixed raw = streamWriter.flush := by
    have hbits : 3 < 2 ^ 3 := by decide
    have hconcat := writeBits_concat hdr0 3 payloadBits.1 3 payloadBits.2 hbits
    calc
      deflateFixed raw = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := hdeflateBits
      _ = (BitWriter.writeBits (BitWriter.writeBits hdr0 3 3) payloadBits.1 payloadBits.2).flush := by
            simp [hbw2]
      _ = streamWriter.flush := by
            simpa [streamWriter, streamBits, streamLen] using (congrArg BitWriter.flush hconcat).symm
  have hmod3 : streamBits % 2 ^ 3 = 3 := by
    have h := mod_two_pow_or_shift (a := 3) (b := payloadBits.1) (k := 3) (len := 3) (by decide)
    simpa [streamBits] using h
  have hprefix : BitWriter.writeBits hdr0 streamBits 3 = hdrHeader := by
    have hbw2' : BitWriter.writeBits hdr0 3 3 = hdrHeader := by
      simpa using hbw2.symm
    calc
      BitWriter.writeBits hdr0 streamBits 3 =
          BitWriter.writeBits hdr0 (streamBits % 2 ^ 3) 3 := by
            simpa using (writeBits_mod hdr0 streamBits 3)
      _ = BitWriter.writeBits hdr0 3 3 := by
            simp [hmod3]
      _ = hdrHeader := hbw2'
  -- Reader at the start of the deflated stream.
  let streamReader0 : BitReader := {
    data := streamWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  have hbw0 : hdr0.bitPos = 0 := rfl
  have hbw0out : hdr0.out.size = 0 := by
    simp [hdr0, BitWriter.empty]
  have hbr0 :
      streamReader0 = BitWriter.readerAt hdr0 streamWriter.flush
        (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide) := by
    apply BitReader.ext <;> simp [streamReader0, BitWriter.readerAt, hdr0, hbw0, hbw0out]
  let streamReaderHeader := BitWriter.readerAt hdrHeader streamWriter.flush
      (by
        simpa [hprefix] using
          (flush_size_writeBits_prefix (bw := hdr0) (bits := streamBits) (k := 3)
            (len := streamLen) (hk := by omega)))
      (by
        simpa [hprefix] using
          (bitPos_lt_8_writeBits hdr0 streamBits 3 (by decide)))
  have hread0_at :
      (BitWriter.readerAt hdr0 streamWriter.flush
        (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide)).bitIndex + 3 ≤
        (BitWriter.readerAt hdr0 streamWriter.flush
          (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide)).data.size * 8 := by
    simpa using
      (readerAt_writeBits_bound (bw := hdr0) (bits := streamBits) (len := streamLen) (k := 3)
        (hk := by omega) (hbit := by decide))
  have hread0 : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [hbr0] using hread0_at
  have hread3 : streamReader0.readBits 3 hread0 = (3, streamReaderHeader) := by
    have h' :=
      (readBits_readerAt_writeBits_prefix (bw := hdr0) (bits := streamBits) (len := streamLen)
        (k := 3) (hk := by omega) (hbit := by decide) (hcur := curClearAbove_empty)
        (hread := hread0_at))
    dsimp at h'
    have h'br : streamReader0.readBits 3 hread0_at = (3, streamReaderHeader) := by
      -- rewrite with the collapsed header bits and prefix reader
      simpa [hbr0, hmod3, hprefix, streamReaderHeader, hdr0, hbw0] using h'
    have hirrel : streamReader0.readBits 3 hread0 = streamReader0.readBits 3 hread0_at :=
      readBits_proof_irrel (br := streamReader0) (n := 3) hread0 hread0_at
    exact hirrel.trans h'br
  -- Final reader after the fixed literal stream.
  have hflushFinal :
      (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush.size ≤ streamWriter.flush.size := by
    have hEq : streamWriter.flush = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := by
      exact hdeflateTotal.symm.trans hdeflateBits
    simp [hEq]
  let streamReaderFinal := BitWriter.readerAt (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2) streamWriter.flush
    hflushFinal
    (bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2
      (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide))))
  -- Evaluate the block decoder once.
  have hloop :
      zlibDecompressLoop streamReader0 ByteArray.empty =
        some (streamReaderFinal, raw) := by
    -- unfold and simplify the fixed-block path
    have hdecodeLit : decodeFixedLiteralBlock streamReaderHeader ByteArray.empty =
        some (streamReaderFinal, raw) := by
      simpa [streamReaderFinal, hdeflateTotal, streamWriter] using hdecode
    have hdecode' : decodeFixedBlock streamReaderHeader ByteArray.empty =
        some (streamReaderFinal, raw) := by
      simp [decodeFixedBlock, decodeFixedBlockFast, hdecodeLit]
    -- Evaluate the loop body (bfinal = 1, btype = 1).
    have hbfinal : (3 % 2) = 1 := by decide
    have hbtype' : ((3 >>> 1) % 4) = 1 := by decide
    have hcond : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := hread0
    have hread3' : streamReader0.readBits 3 hcond = (3, streamReaderHeader) := by
      simpa using hread3
    simp [zlibDecompressLoop, zlibDecompressLoopFuel, hcond, hread3', hdecode', hbfinal]
  -- Evaluate the decompressor on the fixed-compression stream.
  unfold zlibDecompress
  -- simplify header checks and the deflated slice
  simp [bytes, hcmf, hflg, hmod, hbtype, hflg0, hdeflated, hdeflateTotal, streamWriter]
  -- replace the loop with its computed result
  rw [hloop]
  -- compute the Adler position and value
  have hAlign : streamReaderFinal.alignByte.bytePos = streamWriter.flush.size := by
    -- `streamReaderFinal` reads from the flush itself
    simpa [streamReaderFinal] using
      (readerAt_alignByte_bytePos_eq_data
        (bw := BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2)
        (data := streamWriter.flush)
        (hflush := hflushFinal)
        (hbit := bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2
          (bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide))))
        (hdata := hdeflateTotal.symm.trans hdeflateBits))
  have hsize : bytes.size = streamWriter.flush.size + 6 := by
    -- size = deflate + header + adler
    have hsz := zlibCompressFixed_size raw
    simpa [bytes, hdeflateTotal] using hsz
  have hposEq : streamReaderFinal.alignByte.bytePos + 2 = bytes.size - 4 := by
    -- bytes.size = streamWriter.flush.size + 6
    have : streamWriter.flush.size + 2 = (streamWriter.flush.size + 6) - 4 := by omega
    simpa [hAlign, hsize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hAdlerPos' : streamReaderFinal.alignByte.bytePos + 2 + 3 < bytes.size := by
    -- rewrite to the canonical Adler position
    simpa [hposEq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAdlerPos
  have hread : readU32BE bytes (streamReaderFinal.alignByte.bytePos + 2) hAdlerPos' = (adler32 raw).toNat := by
    simpa [hposEq, readU32BE_proof_irrel] using hadler
  -- close the final Adler check
  simp [hAdlerPos', hread, bytes]

-- Zlib decompression of dynamic-compression output yields the original bytes.
lemma zlibDecompress_zlibCompressDynamic (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressDynamic raw).size) :
    zlibDecompress (zlibCompressDynamic raw) hsize = some raw := by
  have hz : zlibCompressDynamic raw = zlibCompressFixed raw := by
    rfl
  have hsizeFixed : 2 ≤ (zlibCompressFixed raw).size := by
    simpa [hz] using hsize
  simpa [hz] using
    (zlibDecompress_zlibCompressFixed (raw := raw) (hsize := hsizeFixed))

end Lemmas

end Bitmaps
