import Bitmap.Lemmas.Png.MultiIdatPreChunkContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `pHYs` (Step 2b, refactored) -/

structure PhysChunkWitness where
  payload : ByteArray
  physical : PngPhysicalPixelDimensions
  hParses : parsePhysData payload = some physical

lemma PhysChunkWitness.payload_size (w : PhysChunkWitness) : w.payload.size = 9 := by
  have h := w.hParses
  unfold parsePhysData at h
  by_contra hne
  simp [hne] at h

def PhysChunkWitness.toPreIdat (w : PhysChunkWitness) (hdr : PngHeader) :
    PreIdatChunk hdr where
  typeBytes := physTypeBytes
  hTypeSize := by rfl
  hTypeNotIDAT := by decide
  hTypeNotIHDR := by decide
  payload := w.payload
  hPayloadFits := by rw [w.payload_size]; decide
  expectedMetadata := { PngMetadata.empty with physical := some w.physical }
  hAcceptStep := by
    intro fuel bytes pos state hpos hLen hread hheader _hPLTE hIDAT _hClosed hMetaEmpty
    have hNotIHDR : (physTypeBytes == ihdrTypeBytes) = false := by decide
    have hNotPLTE : (physTypeBytes == plteTypeBytes) = false := by decide
    have hNotIDAT : (physTypeBytes == idatTypeBytes) = false := by decide
    have hNotIEND : (physTypeBytes == iendTypeBytes) = false := by decide
    have hNotTRNS : (physTypeBytes == trnsTypeBytes) = false := by decide
    have hNotBKGD : (physTypeBytes == bkgdTypeBytes) = false := by decide
    have hNotGAMA : (physTypeBytes == gamaTypeBytes) = false := by decide
    have hNotCHRM : (physTypeBytes == chrmTypeBytes) = false := by decide
    have hNotSRGB : (physTypeBytes == srgbTypeBytes) = false := by decide
    have hNotTIME : (physTypeBytes == timeTypeBytes) = false := by decide
    have hIsPHYS : (physTypeBytes == physTypeBytes) = true := by decide
    have hDup : state.metadata.physical.isSome = false := by
      rw [hMetaEmpty]; rfl
    have hStep := parsePngLoopFuelWithMetadata_accepts_pHYs fuel bytes pos state
      hdr physTypeBytes w.payload (pos + 8 + w.payload.size + 4) w.physical
      hpos hLen hread hheader
      hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS hNotBKGD
      hNotGAMA hNotCHRM hNotSRGB hNotTIME hIsPHYS hIDAT hDup w.hParses
    rw [hStep]
    show parsePngLoopFuelWithMetadata fuel bytes (pos + 8 + w.payload.size + 4)
      { state with metadata :=
          { state.metadata with physical := some w.physical } } = _
    congr 1
    rw [hMetaEmpty]

structure MultiIdatPhysContainerSpec where
  header : PngHeader
  idatChunks : List ByteArray
  hChunkSize : ∀ c, c ∈ idatChunks → c.size < 2 ^ 32
  hNonempty : idatChunks ≠ []
  hBitDepth : header.bitDepth = 1 ∨ header.bitDepth = 8 ∨ header.bitDepth = 16
  hColorType :
    header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6
  hCtBdSupported :
    pngColorTypeBitDepthSupported header.colorType header.bitDepth = true
  hInterlace : header.interlace = 0
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32
  pHYs : Option PhysChunkWitness

namespace MultiIdatPhysContainerSpec

variable (s : MultiIdatPhysContainerSpec)

def toGeneric : MultiIdatGenericPreChunkContainerSpec where
  header := s.header
  idatChunks := s.idatChunks
  hChunkSize := s.hChunkSize
  hNonempty := s.hNonempty
  hBitDepth := s.hBitDepth
  hColorType := s.hColorType
  hCtBdSupported := s.hCtBdSupported
  hInterlace := s.hInterlace
  hWidth := s.hWidth
  hHeight := s.hHeight
  preChunk := s.pHYs.map (·.toPreIdat s.header)

def bytes : ByteArray := s.toGeneric.bytes
def idatData : ByteArray := s.toGeneric.idatData
def expectedMetadata : PngMetadata := s.toGeneric.expectedMetadata
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := s.toGeneric.bytes_size_ge_8

theorem parsePngForDecode_multiIdatPhysContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } :=
  s.toGeneric.parsePngForDecode_correct

end MultiIdatPhysContainerSpec

end Lemmas

end Bitmaps
