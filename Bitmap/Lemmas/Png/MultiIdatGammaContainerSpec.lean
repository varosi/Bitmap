import Bitmap.Lemmas.Png.MultiIdatPreChunkContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `gAMA` (Step 2c gAMA, refactored) -/

structure GammaChunkWitness where
  payload : ByteArray
  gamma : Nat
  hParses : parseGammaData payload = some gamma

lemma GammaChunkWitness.payload_size (w : GammaChunkWitness) : w.payload.size = 4 := by
  have h := w.hParses
  unfold parseGammaData at h
  by_contra hne
  simp [hne] at h

def GammaChunkWitness.toPreIdat (w : GammaChunkWitness) (hdr : PngHeader) :
    PreIdatChunk hdr where
  typeBytes := gamaTypeBytes
  hTypeSize := by rfl
  hTypeNotIDAT := by decide
  hTypeNotIHDR := by decide
  payload := w.payload
  hPayloadFits := by rw [w.payload_size]; decide
  expectedMetadata := { PngMetadata.empty with gamma := some w.gamma }
  hAcceptStep := by
    intro fuel bytes pos state hpos hLen hread hheader hPLTE hIDAT _hClosed hMetaEmpty
    have hNotIHDR : (gamaTypeBytes == ihdrTypeBytes) = false := by decide
    have hNotPLTE : (gamaTypeBytes == plteTypeBytes) = false := by decide
    have hNotIDAT : (gamaTypeBytes == idatTypeBytes) = false := by decide
    have hNotIEND : (gamaTypeBytes == iendTypeBytes) = false := by decide
    have hNotTRNS : (gamaTypeBytes == trnsTypeBytes) = false := by decide
    have hNotBKGD : (gamaTypeBytes == bkgdTypeBytes) = false := by decide
    have hIsGAMA : (gamaTypeBytes == gamaTypeBytes) = true := by decide
    have hOrder : (state.seenPLTE || state.seenIDAT) = false := by
      rw [hPLTE, hIDAT]; rfl
    have hDup : state.metadata.gamma.isSome = false := by
      rw [hMetaEmpty]; rfl
    have hSrgb : state.metadata.srgb = none := by
      rw [hMetaEmpty]; rfl
    have hStep := parsePngLoopFuelWithMetadata_accepts_gAMA fuel bytes pos state
      hdr gamaTypeBytes w.payload (pos + 8 + w.payload.size + 4) w.gamma
      hpos hLen hread hheader
      hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS hNotBKGD
      hIsGAMA hOrder hDup hSrgb w.hParses
    rw [hStep]
    show parsePngLoopFuelWithMetadata fuel bytes (pos + 8 + w.payload.size + 4)
      { state with metadata :=
          { state.metadata with gamma := some w.gamma } } = _
    congr 1
    rw [hMetaEmpty]

structure MultiIdatGammaContainerSpec where
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
  gAMA : Option GammaChunkWitness

namespace MultiIdatGammaContainerSpec

variable (s : MultiIdatGammaContainerSpec)

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
  preChunk := s.gAMA.map (·.toPreIdat s.header)

def bytes : ByteArray := s.toGeneric.bytes
def idatData : ByteArray := s.toGeneric.idatData
def expectedMetadata : PngMetadata := s.toGeneric.expectedMetadata
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := s.toGeneric.bytes_size_ge_8

theorem parsePngForDecode_multiIdatGammaContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } :=
  s.toGeneric.parsePngForDecode_correct

end MultiIdatGammaContainerSpec

end Lemmas

end Bitmaps
