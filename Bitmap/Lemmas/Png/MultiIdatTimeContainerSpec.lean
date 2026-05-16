import Bitmap.Lemmas.Png.MultiIdatPreChunkContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `tIME` (Step 2a, refactored)

Built as a thin instantiation of `MultiIdatGenericPreChunkContainerSpec`.
The generic spec carries the byte-layout, position-arithmetic, and
walk infrastructure; this file supplies only the chunk-specific bits:
the witness shape, the `parsePngLoopFuelWithMetadata_accepts_tIME`
plumbing, and the public spec wrapper exposing the conventional
field names (`tIME`, `bytes`, `expectedMetadata`, etc.). -/

/-- A `tIME` chunk witness: 7-byte payload + decoded `PngTime` + round-trip. -/
structure TimeChunkWitness where
  payload : ByteArray
  time : PngTime
  hParses : parseTimeData payload = some time

/-- The witness payload has the canonical 7-byte length (forced by
`parseTimeData`'s size check). -/
lemma TimeChunkWitness.payload_size (w : TimeChunkWitness) : w.payload.size = 7 := by
  have h := w.hParses
  unfold parseTimeData at h
  by_contra hne
  simp [hne] at h

/-- Build a `PreIdatChunk` from a `TimeChunkWitness` by packaging the
accept-step proof for `tIME`. -/
def TimeChunkWitness.toPreIdat (w : TimeChunkWitness) (hdr : PngHeader) :
    PreIdatChunk hdr where
  typeBytes := timeTypeBytes
  hTypeSize := by rfl
  hTypeNotIDAT := by decide
  hTypeNotIHDR := by decide
  payload := w.payload
  hPayloadFits := by rw [w.payload_size]; decide
  expectedMetadata := { PngMetadata.empty with modificationTime := some w.time }
  hAcceptStep := by
    intro fuel bytes pos state hpos hLen hread hheader hPLTE _hIDAT _hClosed hMetaEmpty
    have hNotIHDR : (timeTypeBytes == ihdrTypeBytes) = false := by decide
    have hNotPLTE : (timeTypeBytes == plteTypeBytes) = false := by decide
    have hNotIDAT : (timeTypeBytes == idatTypeBytes) = false := by decide
    have hNotIEND : (timeTypeBytes == iendTypeBytes) = false := by decide
    have hNotTRNS : (timeTypeBytes == trnsTypeBytes) = false := by decide
    have hNotBKGD : (timeTypeBytes == bkgdTypeBytes) = false := by decide
    have hNotGAMA : (timeTypeBytes == gamaTypeBytes) = false := by decide
    have hNotCHRM : (timeTypeBytes == chrmTypeBytes) = false := by decide
    have hNotSRGB : (timeTypeBytes == srgbTypeBytes) = false := by decide
    have hIsTIME : (timeTypeBytes == timeTypeBytes) = true := by decide
    have hDup : state.metadata.modificationTime.isSome = false := by
      rw [hMetaEmpty]; rfl
    have hStep := parsePngLoopFuelWithMetadata_accepts_tIME fuel bytes pos state
      hdr timeTypeBytes w.payload (pos + 8 + w.payload.size + 4) w.time
      hpos hLen hread hheader
      hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS hNotBKGD
      hNotGAMA hNotCHRM hNotSRGB hIsTIME hDup w.hParses
    rw [hStep]
    -- The resulting state has `closedIDAT := if state.seenIDAT then true else
    -- state.closedIDAT`. Since hIDAT : state.seenIDAT = false, the if-branch
    -- reduces to state.closedIDAT.
    show parsePngLoopFuelWithMetadata fuel bytes (pos + 8 + w.payload.size + 4)
      { state with
          closedIDAT := if state.seenIDAT then true else state.closedIDAT
          metadata := { state.metadata with modificationTime := some w.time } } = _
    congr 1
    rw [hMetaEmpty]
    rw [_hIDAT]
    simp

/-- A PNG byte stream with the multi-IDAT shape plus an optional `tIME`
chunk between IHDR and the first IDAT. -/
structure MultiIdatTimeContainerSpec where
  header : PngHeader
  idatChunks : List ByteArray
  hChunkSize : ∀ c, c ∈ idatChunks → c.size < 2 ^ 32
  hNonempty : idatChunks ≠ []
  hBitDepth : header.bitDepth = 8 ∨ header.bitDepth = 16
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

/-- Convert to the generic pre-chunk spec, mapping `tIME` to its
`PreIdatChunk` wrapper. -/
def toGeneric : MultiIdatGenericPreChunkContainerSpec where
  header := s.header
  idatChunks := s.idatChunks
  hChunkSize := s.hChunkSize
  hNonempty := s.hNonempty
  hBitDepth := s.hBitDepth
  hColorType := s.hColorType
  hInterlace := s.hInterlace
  hWidth := s.hWidth
  hHeight := s.hHeight
  preChunk := s.tIME.map (·.toPreIdat s.header)

def bytes : ByteArray := s.toGeneric.bytes
def idatData : ByteArray := s.toGeneric.idatData
def expectedMetadata : PngMetadata := s.toGeneric.expectedMetadata
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := s.toGeneric.bytes_size_ge_8

/-- The metadata-aware parser accepts any `MultiIdatTimeContainerSpec`
byte stream and returns the expected header, IDAT, and metadata. -/
theorem parsePngForDecode_multiIdatTimeContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } :=
  s.toGeneric.parsePngForDecode_correct

end MultiIdatTimeContainerSpec

end Lemmas

end Bitmaps
