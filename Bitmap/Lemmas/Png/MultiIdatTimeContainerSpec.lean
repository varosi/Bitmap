import Bitmap.Lemmas.Png.MultiIdatContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `tIME` (Step 2a)

`MultiIdatTimeContainerSpec` extends `MultiIdatContainerSpec` with an
optional `tIME` chunk placed between IHDR and the first IDAT. This is
the simplest ancillary-chunk extension: `tIME` carries a modification
timestamp that does not affect the decoder's color flow, so the
existing end-to-end pipeline applies almost verbatim.

The byte layout is

    signature ++ IHDR ++ (tIME chunk, if any) ++ IDAT* ++ IEND.

The decoder pipeline records the parsed `PngTime` in the metadata's
`modificationTime` field. Because `applyPngColorSpaceTransform` only
inspects the `srgb`/`chromaticities`/`gamma` fields, a `modificationTime`-
only metadata behaves identically to `PngMetadata.empty` under the
color-space transform. -/

/-- A `tIME` chunk witness: the raw 7-byte payload plus the decoded
`PngTime` and the round-trip witness `parseTimeData payload = some time`. -/
structure TimeChunkWitness where
  payload : ByteArray
  time : PngTime
  hParses : parseTimeData payload = some time

/-- A PNG byte stream with the multi-IDAT shape plus an optional `tIME`
chunk between IHDR and the first IDAT. -/
structure MultiIdatTimeContainerSpec where
  header : PngHeader
  idatChunks : List ByteArray
  hChunkSize : ∀ c, c ∈ idatChunks → c.size < 2 ^ 32
  hNonempty : idatChunks ≠ []
  hBitDepth : header.bitDepth = 8
  hColorType :
    header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6
  hInterlace : header.interlace = 0
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32
  /-- Optional `tIME` chunk placed between IHDR and the first IDAT. -/
  tIME : Option TimeChunkWitness

namespace MultiIdatTimeContainerSpec

variable (s : MultiIdatTimeContainerSpec)

/-- The underlying multi-IDAT spec (forgetting the `tIME` data). -/
def toMulti : MultiIdatContainerSpec where
  header := s.header
  idatChunks := s.idatChunks
  hChunkSize := s.hChunkSize
  hNonempty := s.hNonempty
  hBitDepth := s.hBitDepth
  hColorType := s.hColorType
  hInterlace := s.hInterlace
  hWidth := s.hWidth
  hHeight := s.hHeight

/-- The wrapped `tIME` chunk bytes (12-byte overhead + 7-byte payload), or
the empty byte array when no `tIME` chunk is present. -/
def timeChunkBytes : ByteArray :=
  match s.tIME with
  | none => ByteArray.empty
  | some w => mkChunkBytes timeTypeBytes w.payload

/-- Wire size of the `tIME` chunk: 19 bytes when present, 0 otherwise. -/
def tIMEWireSize : Nat :=
  if s.tIME.isSome then 19 else 0

/-- The byte layout: signature, IHDR, optional tIME, concatenated IDATs, IEND. -/
def bytes : ByteArray :=
  pngSignature ++
  mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
  s.timeChunkBytes ++
  s.toMulti.idatChunksBytes ++
  mkChunkBytes iendTypeBytes ByteArray.empty

/-- The concatenated IDAT payload — same as the underlying multi-IDAT. -/
def idatData : ByteArray :=
  s.toMulti.idatData

/-- The metadata produced by parsing the byte stream: empty plus the
`tIME` modificationTime, if any. -/
def expectedMetadata : PngMetadata :=
  match s.tIME with
  | none => PngMetadata.empty
  | some w => { PngMetadata.empty with modificationTime := some w.time }

/-- Bytes layout reduces to the multi-IDAT layout when no `tIME` is present. -/
lemma bytes_eq_multi_of_none (h : s.tIME = none) :
    s.bytes = s.toMulti.bytes := by
  unfold bytes toMulti MultiIdatContainerSpec.bytes timeChunkBytes
  rw [h]
  simp

/-- The expected metadata is empty when no `tIME` is present. -/
lemma expectedMetadata_of_none (h : s.tIME = none) :
    s.expectedMetadata = PngMetadata.empty := by
  unfold expectedMetadata; rw [h]

/-! ### Forward correctness — `tIME = none` case via the multi-IDAT theorem -/

/-- When no `tIME` chunk is present, the multi-IDAT-with-time spec
reduces to a plain `MultiIdatContainerSpec`, and the
`parsePngForDecode` correctness theorem follows from
`parsePngForDecode_multiIdatContainerSpec_correct`. -/
theorem parsePngForDecode_multiIdatTimeContainerSpec_correct_of_none
    (h : s.tIME = none) :
    parsePngForDecode s.bytes
        (by rw [bytes_eq_multi_of_none s h]; exact s.toMulti.bytes_size_ge_8) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  rw [expectedMetadata_of_none s h]
  have hMulti := s.toMulti.parsePngForDecode_multiIdatContainerSpec_correct
  -- Bytes equality lets us route the parseForDecode call through toMulti.
  have hBytesEq : s.bytes = s.toMulti.bytes := bytes_eq_multi_of_none s h
  have hCongr :
      parsePngForDecode s.bytes
        (hBytesEq ▸ s.toMulti.bytes_size_ge_8) =
      parsePngForDecode s.toMulti.bytes s.toMulti.bytes_size_ge_8 := by
    congr 1
  rw [hCongr]
  -- toMulti.idatData = s.idatData definitionally (same idatChunks).
  show parsePngForDecode s.toMulti.bytes s.toMulti.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := PngMetadata.empty }
  -- s.toMulti.header = s.header by rfl, s.toMulti.idatData = s.idatData by rfl
  exact hMulti

end MultiIdatTimeContainerSpec

end Lemmas

end Bitmaps
