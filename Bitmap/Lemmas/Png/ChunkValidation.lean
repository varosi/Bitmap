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
    (hcritical : isCriticalChunkType typBytes = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = none := by
  unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND, hcritical]

/-- Ancillary chunks before the `IDAT` run do not change parser state. -/
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
    (hcritical : isCriticalChunkType typBytes = false)
    (hseen : state.seenIDAT = false) :
    parsePngLoopFuel (fuel + 1) bytes pos state =
      parsePngLoopFuel fuel bytes posNext state := by
  conv =>
    lhs
    unfold parsePngLoopFuel
  simp [hpos, hLen, hread, hheader, hnotIHDR, hnotPLTE, hnotIDAT, hnotIEND,
    hcritical, hseen]

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
