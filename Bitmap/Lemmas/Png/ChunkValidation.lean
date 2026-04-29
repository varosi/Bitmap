import Bitmap.Png

namespace Bitmaps

namespace Lemmas

open Png

/-- `readChunk` cannot accept a chunk whose stored CRC differs from the
computed CRC over the parsed type and payload bytes. -/
lemma readChunk_rejects_crc_mismatch (bytes : ByteArray) (pos : Nat)
    (hLen : pos + 3 < bytes.size)
    (hBound : pos + 8 + readU32BE bytes pos hLen + 4 ≤ bytes.size)
    (hBad :
      readU32BE bytes (pos + 8 + readU32BE bytes pos hLen) (by omega) ≠
        (crc32Chunk
          (bytes.extract (pos + 4) (pos + 4 + 4))
          (bytes.extract (pos + 8) (pos + 8 + readU32BE bytes pos hLen))).toNat) :
    readChunk bytes pos hLen = none := by
  unfold readChunk
  simp [hBound, hBad]

/-- Every successful `readChunk` result passed the CRC equality checked by the
runtime parser. This is the soundness direction for chunk CRC validation. -/
lemma readChunk_success_crc_matches (bytes : ByteArray) (pos : Nat)
    (hLen : pos + 3 < bytes.size)
    (hread : (readChunk bytes pos hLen).isSome) :
    ∃ hBound : pos + 8 + readU32BE bytes pos hLen + 4 ≤ bytes.size,
      readU32BE bytes (pos + 8 + readU32BE bytes pos hLen) (by omega) =
        (crc32Chunk
          (bytes.extract (pos + 4) (pos + 4 + 4))
          (bytes.extract (pos + 8) (pos + 8 + readU32BE bytes pos hLen))).toNat := by
  unfold readChunk at hread
  by_cases hBound : pos + 8 + readU32BE bytes pos hLen + 4 ≤ bytes.size
  · simp [hBound] at hread
    refine ⟨hBound, ?_⟩
    simpa using hread
  · simp [hBound] at hread

/-- Before `IHDR`, the block-stream parser rejects every non-`IHDR` chunk. -/
lemma parsePngLoopFuel_rejects_non_ihdr_before_header (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = none)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR]

/-- Once an `IHDR` has been accepted, any later `IHDR` is rejected. -/
lemma parsePngLoopFuel_rejects_duplicate_ihdr (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hIHDR : (typBytes == ihdrTypeBytes) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hIHDR]

/-- `PLTE` is rejected after another `PLTE` or after any `IDAT`. -/
lemma parsePngLoopFuel_rejects_plte_after_plte_or_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hPLTE : (typBytes == plteTypeBytes) = true)
    (hseen : (state.seenPLTE || state.seenIDAT) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hPLTE, hseen]

/-- After an ancillary chunk closes the `IDAT` run, another `IDAT` is rejected. -/
lemma parsePngLoopFuel_rejects_idat_after_closed_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hIDAT : (typBytes == idatTypeBytes) = true)
    (hclosed : state.closedIDAT = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hIDAT, hclosed]

/-- An `IEND` chunk with payload bytes is rejected. -/
lemma parsePngLoopFuel_rejects_nonempty_iend (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hIEND : (typBytes == iendTypeBytes) = true)
    (hdata : (chunkData.size != 0) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hIEND, hdata]

/-- `IEND` is rejected until at least one `IDAT` has been seen. -/
lemma parsePngLoopFuel_rejects_iend_before_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hIEND : (typBytes == iendTypeBytes) = true)
    (hdata : (chunkData.size != 0) = false)
    (hseen : state.seenIDAT = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hIEND, hdata, hseen]

/-- `IEND` must consume the final bytes of the PNG stream. -/
lemma parsePngLoopFuel_rejects_trailing_after_iend (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hIEND : (typBytes == iendTypeBytes) = true)
    (hdata : (chunkData.size != 0) = false)
    (hseen : state.seenIDAT = true)
    (htrail : (posNext != bytes.size) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hIEND,
    hdata, hseen, htrail]

/-- A `tRNS` chunk is rejected. tRNS attaches transparency to color types 0/2/3 that
the decoder does not honor; silently skipping it would change pixel semantics. -/
lemma parsePngLoopFuel_rejects_tRNS (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND, hTRNS]

/-- The metadata-aware parser records a valid `tRNS` chunk and continues.
This is the branch-level correctness fact for supported transparency metadata. -/
lemma parsePngLoopFuelWithMetadata_accepts_tRNS (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (trns : PngTransparency)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.transparency.isSome = false)
    (hparse : parseTrnsData hdr chunkData = some trns) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with metadata := { state.metadata with transparency := some trns } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hTRNS, hseen, hdup, hparse]

/-- `tRNS` must appear before the first `IDAT` chunk in the metadata-aware parser. -/
lemma parsePngLoopFuelWithMetadata_rejects_tRNS_after_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true)
    (hseen : state.seenIDAT = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hTRNS, hseen]

/-- A second `tRNS` chunk is rejected rather than replacing earlier metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_tRNS (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hTRNS : (typBytes == trnsTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.transparency.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hTRNS, hseen, hdup]

/-- The metadata-aware parser records a valid `bKGD` chunk and continues.
This proves background metadata is preserved at the container layer. -/
lemma parsePngLoopFuelWithMetadata_accepts_bKGD (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (bkgd : PngBackground)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hBKGD : (typBytes == bkgdTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.background.isSome = false)
    (hparse : parseBkgdData hdr chunkData = some bkgd) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      parsePngLoopFuelWithMetadata fuel bytes posNext
        { state with metadata := { state.metadata with background := some bkgd } } := by
  conv =>
    lhs
    unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hBKGD, hseen, hdup, hparse]

/-- `bKGD` must appear before the first `IDAT` chunk in the metadata-aware parser. -/
lemma parsePngLoopFuelWithMetadata_rejects_bKGD_after_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hBKGD : (typBytes == bkgdTypeBytes) = true)
    (hseen : state.seenIDAT = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hBKGD, hseen]

/-- A second `bKGD` chunk is rejected rather than replacing earlier metadata. -/
lemma parsePngLoopFuelWithMetadata_rejects_duplicate_bKGD (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hBKGD : (typBytes == bkgdTypeBytes) = true)
    (hseen : state.seenIDAT = false)
    (hdup : state.metadata.background.isSome = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hBKGD, hseen, hdup]

/-- Once transparency or background metadata has appeared, a later `PLTE` is
rejected so the parser enforces the required relative chunk order. -/
lemma parsePngLoopFuelWithMetadata_rejects_plte_after_metadata (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hPLTE : (typBytes == plteTypeBytes) = true)
    (hseen : (state.seenPLTE || state.seenIDAT) = false)
    (hmetadata : (state.metadata.transparency.isSome || state.metadata.background.isSome) = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuelWithMetadata
  simp [hpos, hLen, hread, hheader, hnotIHDR, hPLTE, hseen, hmetadata]

/-- An `sBIT` chunk is rejected. sBIT records the original significant bit count per
channel; silently skipping it would misrepresent pixel precision. -/
lemma parsePngLoopFuel_rejects_sBIT (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hSBIT : (typBytes == sbitTypeBytes) = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND, hnotTRNS, hSBIT]

/-- Unknown critical chunk types are rejected after the header. -/
lemma parsePngLoopFuel_rejects_unknown_critical (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotSBIT : (typBytes == sbitTypeBytes) = false)
    (hcritical : isCriticalChunkType typBytes = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotSBIT, hcritical]

/-- Ancillary chunks (other than the explicitly rejected `tRNS`/`sBIT`) before the
`IDAT` run do not change parser state. -/
lemma parsePngLoopFuel_ignores_ancillary_before_idat (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hnotIDAT : (typBytes == idatTypeBytes) = false)
    (hnotIEND : (typBytes == iendTypeBytes) = false)
    (hnotTRNS : (typBytes == trnsTypeBytes) = false)
    (hnotSBIT : (typBytes == sbitTypeBytes) = false)
    (hcritical : isCriticalChunkType typBytes = false)
    (hseen : state.seenIDAT = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state =
      parsePngLoopFuel fuel bytes posNext state := by
  conv =>
    lhs
    unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hnotTRNS, hnotSBIT, hcritical, hseen]

/-- An `IDAT` chunk in an open `IDAT` run appends its payload and continues. -/
lemma parsePngLoopFuel_idat_appends_when_open (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader) (typBytes chunkData : ByteArray) (posNext : Nat)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (typBytes, chunkData, posNext))
    (hheader : state.header = some hdr)
    (hnotIHDR : (typBytes == ihdrTypeBytes) = false)
    (hnotPLTE : (typBytes == plteTypeBytes) = false)
    (hIDAT : (typBytes == idatTypeBytes) = true)
    (hclosed : state.closedIDAT = false)
    (hpalette : (hdr.colorType == 3 && !state.seenPLTE) = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state =
      parsePngLoopFuel fuel bytes posNext
        { header := some hdr
          idat := state.idat ++ chunkData
          seenPLTE := state.seenPLTE
          seenIDAT := true
          closedIDAT := false } := by
  conv =>
    lhs
    unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hIDAT, hclosed, hpalette]

end Lemmas

end Bitmaps
