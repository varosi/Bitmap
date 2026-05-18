import Bitmap.Lemmas.Png.MultiIdatPreChunkContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `cHRM` (Step 2c cHRM, refactored) -/

structure ChrmChunkWitness where
  payload : ByteArray
  chrm : PngChromaticities
  hParses : parseChrmData payload = some chrm

lemma ChrmChunkWitness.payload_size (w : ChrmChunkWitness) : w.payload.size = 32 := by
  have h := w.hParses
  unfold parseChrmData at h
  by_contra hne
  simp [hne] at h

def ChrmChunkWitness.toPreIdat (w : ChrmChunkWitness) (hdr : PngHeader) :
    PreIdatChunk hdr where
  typeBytes := chrmTypeBytes
  hTypeSize := by rfl
  hTypeNotIDAT := by decide
  hTypeNotIHDR := by decide
  payload := w.payload
  hPayloadFits := by rw [w.payload_size]; decide
  expectedMetadata := { PngMetadata.empty with chromaticities := some w.chrm }
  hAcceptStep := by
    intro fuel bytes pos state hpos hLen hread hheader hPLTE hIDAT _hClosed hMetaEmpty
    have hNotIHDR : (chrmTypeBytes == ihdrTypeBytes) = false := by decide
    have hNotPLTE : (chrmTypeBytes == plteTypeBytes) = false := by decide
    have hNotIDAT : (chrmTypeBytes == idatTypeBytes) = false := by decide
    have hNotIEND : (chrmTypeBytes == iendTypeBytes) = false := by decide
    have hNotTRNS : (chrmTypeBytes == trnsTypeBytes) = false := by decide
    have hNotBKGD : (chrmTypeBytes == bkgdTypeBytes) = false := by decide
    have hNotGAMA : (chrmTypeBytes == gamaTypeBytes) = false := by decide
    have hIsCHRM : (chrmTypeBytes == chrmTypeBytes) = true := by decide
    have hOrder : (state.seenPLTE || state.seenIDAT) = false := by
      rw [hPLTE, hIDAT]; rfl
    have hDup : state.metadata.chromaticities.isSome = false := by
      rw [hMetaEmpty]; rfl
    have hSrgb : state.metadata.srgb = none := by
      rw [hMetaEmpty]; rfl
    have hStep := parsePngLoopFuelWithMetadata_accepts_cHRM fuel bytes pos state
      hdr chrmTypeBytes w.payload (pos + 8 + w.payload.size + 4) w.chrm
      hpos hLen hread hheader
      hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS hNotBKGD hNotGAMA
      hIsCHRM hOrder hDup hSrgb w.hParses
    rw [hStep]
    show parsePngLoopFuelWithMetadata fuel bytes (pos + 8 + w.payload.size + 4)
      { state with metadata :=
          { state.metadata with chromaticities := some w.chrm } } = _
    congr 1
    rw [hMetaEmpty]

structure MultiIdatChrmContainerSpec where
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
  hInterlace : header.interlace = 0 ∨ header.interlace = 1
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32
  cHRM : Option ChrmChunkWitness

namespace MultiIdatChrmContainerSpec

variable (s : MultiIdatChrmContainerSpec)

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
  preChunk := s.cHRM.map (·.toPreIdat s.header)

def bytes : ByteArray := s.toGeneric.bytes
def idatData : ByteArray := s.toGeneric.idatData
def expectedMetadata : PngMetadata := s.toGeneric.expectedMetadata
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := s.toGeneric.bytes_size_ge_8

theorem parsePngForDecode_multiIdatChrmContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } :=
  s.toGeneric.parsePngForDecode_correct

end MultiIdatChrmContainerSpec

end Lemmas

end Bitmaps
