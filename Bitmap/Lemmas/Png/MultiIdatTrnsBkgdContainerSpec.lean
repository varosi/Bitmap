import Bitmap.Lemmas.Png.MultiIdatTrnsContainerSpec
import Bitmap.Lemmas.Png.MultiIdatBkgdContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container with both tRNS and bKGD pre-IDAT chunks

`MultiIdatTrnsBkgdContainerSpec` describes a PNG byte stream with the
multi-IDAT shape plus a tRNS chunk *and* a bKGD chunk, both placed
between IHDR and the first IDAT (in that order). This is the container
shape needed for `decodeBitmapWithMetadata`'s tRNS-over-background
forward path (target RGB / RGB16 / RGB-from-16-bit-source), which
requires both metadata fields populated.

The container threads two chained walk steps through the metadata-aware
parser, using the underlying `parsePngLoopFuelWithMetadata_accepts_tRNS`
and `_accepts_bKGD` lemmas (whose state updates merge into existing
metadata rather than overwriting). -/

structure MultiIdatTrnsBkgdContainerSpec where
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
  /-- The tRNS chunk witness (mandatory). -/
  trnsWitness : TrnsChunkWitness header
  /-- The bKGD chunk witness (mandatory). -/
  bkgdWitness : BkgdChunkWitness header

namespace MultiIdatTrnsBkgdContainerSpec

variable (s : MultiIdatTrnsBkgdContainerSpec)

/-- The underlying multi-IDAT spec (forgetting both pre-chunks). -/
def toMulti : MultiIdatContainerSpec where
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

/-- The on-the-wire bytes:
    signature ++ IHDR ++ tRNS chunk ++ bKGD chunk ++ IDATs ++ IEND. -/
def bytes : ByteArray :=
  pngSignature ++
  mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
  mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
  mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
  s.toMulti.idatChunksBytes ++
  mkChunkBytes iendTypeBytes ByteArray.empty

def idatData : ByteArray := s.toMulti.idatData

/-- The expected metadata after parsing: both transparency and background. -/
def expectedMetadata : PngMetadata :=
  { PngMetadata.empty with
      transparency := some s.trnsWitness.trns
      background := some s.bkgdWitness.bkgd }

/-- The tRNS chunk's wire size: 12 bytes of overhead + payload. -/
def trnsWireSize : Nat := 12 + s.trnsWitness.payload.size

/-- The bKGD chunk's wire size. -/
def bkgdWireSize : Nat := 12 + s.bkgdWitness.payload.size

/-- The byte position of the bKGD chunk start = 33 + trnsWireSize. -/
def bkgdOffset : Nat := 33 + s.trnsWireSize

/-- The byte position of the first IDAT chunk start. -/
def firstIdatOffset : Nat := s.bkgdOffset + s.bkgdWireSize

/-! ### Size lemmas -/

lemma trnsBytes_size :
    (mkChunkBytes trnsTypeBytes s.trnsWitness.payload).size = s.trnsWireSize := by
  rw [mkChunkBytes_size _ _ (by rfl : trnsTypeBytes.size = 4)]
  unfold trnsWireSize; omega

lemma bkgdBytes_size :
    (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload).size = s.bkgdWireSize := by
  rw [mkChunkBytes_size _ _ (by rfl : bkgdTypeBytes.size = 4)]
  unfold bkgdWireSize; omega

lemma bytes_size :
    s.bytes.size =
      45 + s.trnsWireSize + s.bkgdWireSize + s.toMulti.idatTotalWireSize := by
  unfold bytes
  have hIhdrSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  have hIendSize :
      (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]; simp
  have hTrnsSize := s.trnsBytes_size
  have hBkgdSize := s.bkgdBytes_size
  have hIdatSize :
      s.toMulti.idatChunksBytes.size = s.toMulti.idatTotalWireSize := by
    unfold MultiIdatContainerSpec.idatTotalWireSize
    rw [MultiIdatContainerSpec.idatChunksBytes_size]
    show s.toMulti.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 =
      MultiIdatContainerSpec.idatPrefixWireSize s.toMulti.idatChunks
        s.toMulti.idatChunks.length
    unfold MultiIdatContainerSpec.idatPrefixWireSize
    rw [List.take_length]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_append, ByteArray.size_append,
      pngSignature_size, hIhdrSize, hTrnsSize, hBkgdSize, hIdatSize, hIendSize]
  omega

lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := by
  rw [bytes_size]; omega

end MultiIdatTrnsBkgdContainerSpec

end Lemmas

end Bitmaps
