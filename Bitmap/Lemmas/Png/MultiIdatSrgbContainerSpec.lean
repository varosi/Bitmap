import Bitmap.Lemmas.Png.MultiIdatPreChunkContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `sRGB` (Step 2c sRGB, refactored) -/

structure SrgbChunkWitness where
  payload : ByteArray
  srgb : PngSrgbIntent
  hParses : parseSrgbData payload = some srgb

lemma SrgbChunkWitness.payload_size (w : SrgbChunkWitness) : w.payload.size = 1 := by
  have h := w.hParses
  unfold parseSrgbData at h
  by_contra hne
  simp [hne] at h

def SrgbChunkWitness.toPreIdat (w : SrgbChunkWitness) (hdr : PngHeader) :
    PreIdatChunk hdr where
  typeBytes := srgbTypeBytes
  hTypeSize := by rfl
  hTypeNotIDAT := by decide
  hTypeNotIHDR := by decide
  payload := w.payload
  hPayloadFits := by rw [w.payload_size]; decide
  expectedMetadata := { PngMetadata.empty with srgb := some w.srgb }
  hAcceptStep := by
    intro fuel bytes pos state hpos hLen hread hheader hPLTE hIDAT _hClosed hMetaEmpty
    have hNotIHDR : (srgbTypeBytes == ihdrTypeBytes) = false := by decide
    have hNotPLTE : (srgbTypeBytes == plteTypeBytes) = false := by decide
    have hNotIDAT : (srgbTypeBytes == idatTypeBytes) = false := by decide
    have hNotIEND : (srgbTypeBytes == iendTypeBytes) = false := by decide
    have hNotTRNS : (srgbTypeBytes == trnsTypeBytes) = false := by decide
    have hNotBKGD : (srgbTypeBytes == bkgdTypeBytes) = false := by decide
    have hNotGAMA : (srgbTypeBytes == gamaTypeBytes) = false := by decide
    have hNotCHRM : (srgbTypeBytes == chrmTypeBytes) = false := by decide
    have hIsSRGB : (srgbTypeBytes == srgbTypeBytes) = true := by decide
    have hOrder : (state.seenPLTE || state.seenIDAT) = false := by
      rw [hPLTE, hIDAT]; rfl
    have hDup : state.metadata.srgb.isSome = false := by
      rw [hMetaEmpty]; rfl
    have hGammaNone : state.metadata.gamma = none := by
      rw [hMetaEmpty]; rfl
    have hChrmNone : state.metadata.chromaticities = none := by
      rw [hMetaEmpty]; rfl
    have hStep := parsePngLoopFuelWithMetadata_accepts_sRGB fuel bytes pos state
      hdr srgbTypeBytes w.payload (pos + 8 + w.payload.size + 4) w.srgb
      hpos hLen hread hheader
      hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS hNotBKGD hNotGAMA hNotCHRM
      hIsSRGB hOrder hDup hGammaNone hChrmNone w.hParses
    rw [hStep]
    show parsePngLoopFuelWithMetadata fuel bytes (pos + 8 + w.payload.size + 4)
      { state with metadata :=
          { state.metadata with srgb := some w.srgb } } = _
    congr 1
    rw [hMetaEmpty]

structure MultiIdatSrgbContainerSpec where
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
  sRGB : Option SrgbChunkWitness

namespace MultiIdatSrgbContainerSpec

variable (s : MultiIdatSrgbContainerSpec)

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
  preChunk := s.sRGB.map (·.toPreIdat s.header)

def bytes : ByteArray := s.toGeneric.bytes
def idatData : ByteArray := s.toGeneric.idatData
def expectedMetadata : PngMetadata := s.toGeneric.expectedMetadata
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := s.toGeneric.bytes_size_ge_8

theorem parsePngForDecode_multiIdatSrgbContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } :=
  s.toGeneric.parsePngForDecode_correct

end MultiIdatSrgbContainerSpec

end Lemmas

end Bitmaps
