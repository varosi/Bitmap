import Bitmap.Lemmas.Png.MultiIdatPreChunkContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## tRNS as an instance of the generic pre-chunk container spec (Step 2d) -/

/-- A tRNS chunk witness, parameterised by the surrounding PNG header
(since `parseTrnsData` accepts only 2-byte payloads for `colorType = 0`
and 6-byte payloads for `colorType = 2`; payloads for colorTypes 4 or 6
are rejected entirely). The size constraint is enforced through the
round-trip witness `parseTrnsData hdr payload = some trns`. -/
structure TrnsChunkWitness (hdr : PngHeader) where
  payload : ByteArray
  trns : PngTransparency
  hParses : parseTrnsData hdr payload = some trns
  hPayloadFits : payload.size < 2 ^ 32

/-- Build a `PreIdatChunk` from a `TrnsChunkWitness` by packaging the
accept-step proof for `tRNS`. -/
def TrnsChunkWitness.toPreIdat {hdr : PngHeader} (w : TrnsChunkWitness hdr) :
    PreIdatChunk hdr where
  typeBytes := trnsTypeBytes
  hTypeSize := by rfl
  hTypeNotIDAT := by decide
  hTypeNotIHDR := by decide
  payload := w.payload
  hPayloadFits := w.hPayloadFits
  expectedMetadata := { PngMetadata.empty with transparency := some w.trns }
  hAcceptStep := by
    intro fuel bytes pos state hpos hLen hread hheader hPLTE hIDAT _hClosed hMetaEmpty
    have hNotIHDR : (trnsTypeBytes == ihdrTypeBytes) = false := by decide
    have hNotPLTE : (trnsTypeBytes == plteTypeBytes) = false := by decide
    have hNotIDAT : (trnsTypeBytes == idatTypeBytes) = false := by decide
    have hNotIEND : (trnsTypeBytes == iendTypeBytes) = false := by decide
    have hIsTRNS : (trnsTypeBytes == trnsTypeBytes) = true := by decide
    have hDup : state.metadata.transparency.isSome = false := by
      rw [hMetaEmpty]; rfl
    have hStep := parsePngLoopFuelWithMetadata_accepts_tRNS fuel bytes pos state
      hdr trnsTypeBytes w.payload (pos + 8 + w.payload.size + 4) w.trns
      hpos hLen hread hheader
      hNotIHDR hNotPLTE hNotIDAT hNotIEND
      hIsTRNS hIDAT hDup w.hParses
    rw [hStep]
    -- Rewrite the resulting state to the canonical record-update form.
    show parsePngLoopFuelWithMetadata fuel bytes (pos + 8 + w.payload.size + 4)
      { state with metadata :=
          { state.metadata with transparency := some w.trns } } = _
    congr 1
    rw [hMetaEmpty]

/-- A PNG byte stream with the multi-IDAT shape plus an optional `tRNS`
chunk between IHDR and the first IDAT. Built as a thin wrapper around
the generic `MultiIdatGenericPreChunkContainerSpec`. -/
structure MultiIdatTrnsContainerSpec where
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
  /-- Optional `tRNS` chunk placed between IHDR and the first IDAT. -/
  tRNS : Option (TrnsChunkWitness header)

namespace MultiIdatTrnsContainerSpec

variable (s : MultiIdatTrnsContainerSpec)

/-- Convert to the generic pre-chunk spec, mapping `tRNS` to its
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
  preChunk := s.tRNS.map TrnsChunkWitness.toPreIdat

def bytes : ByteArray := s.toGeneric.bytes
def idatData : ByteArray := s.toGeneric.idatData
def expectedMetadata : PngMetadata := s.toGeneric.expectedMetadata
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := s.toGeneric.bytes_size_ge_8

/-- The metadata-aware parser accepts any `MultiIdatTrnsContainerSpec`
byte stream and returns the expected header, IDAT, and metadata. -/
theorem parsePngForDecode_multiIdatTrnsContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } :=
  s.toGeneric.parsePngForDecode_correct

end MultiIdatTrnsContainerSpec

end Lemmas

end Bitmaps
