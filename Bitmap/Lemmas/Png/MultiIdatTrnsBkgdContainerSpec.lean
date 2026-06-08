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

/-! ### Position arithmetic helpers -/

def idatOffset (i : Nat) : Nat :=
  s.firstIdatOffset + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i

def iendOffset : Nat :=
  s.firstIdatOffset + s.toMulti.idatTotalWireSize

/-! ### Bytes-extract lemmas -/

lemma bytes_eq_signature_then_rest :
    s.bytes =
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
            (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
              (s.toMulti.idatChunksBytes ++
                mkChunkBytes iendTypeBytes ByteArray.empty)))) := by
  unfold bytes
  simp [ByteArray.append_assoc]

lemma bytes_extract_signature : s.bytes.extract 0 8 = pngSignature := by
  rw [s.bytes_eq_signature_then_rest]
  have hSig : pngSignature.size = 8 := pngSignature_size
  rw [byteArray_extract_append_prefix
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
        (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
          (s.toMulti.idatChunksBytes ++
            mkChunkBytes iendTypeBytes ByteArray.empty))))
    (n := 8) (by simp [hSig])]
  rw [← hSig]
  exact ByteArray.extract_zero_size

lemma bytes_extract_skip_signature (start finish : Nat)
    (_h : 8 + finish ≤ s.bytes.size) :
    s.bytes.extract (8 + start) (8 + finish) =
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        (mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
          (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
            (s.toMulti.idatChunksBytes ++
              mkChunkBytes iendTypeBytes ByteArray.empty)))).extract
        start finish := by
  rw [s.bytes_eq_signature_then_rest]
  have hSig : pngSignature.size = 8 := pngSignature_size
  have h' := ByteArray.extract_append_size_add
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
        (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
          (s.toMulti.idatChunksBytes ++
            mkChunkBytes iendTypeBytes ByteArray.empty))))
    (i := start) (j := finish)
  simpa [hSig] using h'

lemma bytes_extract_ihdr :
    s.bytes.extract 8 (8 + 12 + (encodeIHDRData s.header).size) =
      mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hIhdrChunkSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), hIhdrSize]
  rw [hIhdrSize]
  have hSizeBound : 8 + 25 ≤ s.bytes.size := by rw [bytes_size]; omega
  have h := s.bytes_extract_skip_signature 0 25 hSizeBound
  rw [show (8 : Nat) + 0 = 8 from rfl] at h
  rw [show (8 : Nat) + 25 = 8 + 12 + 13 from rfl] at h
  rw [h]
  rw [byteArray_extract_append_prefix
    (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
    (b := mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
      (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)))
    (n := 25) (by rw [hIhdrChunkSize])]
  rw [show (25 : Nat) = (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size from
    hIhdrChunkSize.symm]
  exact ByteArray.extract_zero_size

lemma bytes_extract_skip_through_ihdr (start finish : Nat)
    (_h : 33 + finish ≤ s.bytes.size) :
    s.bytes.extract (33 + start) (33 + finish) =
      (mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
        (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
          (s.toMulti.idatChunksBytes ++
            mkChunkBytes iendTypeBytes ByteArray.empty))).extract
        start finish := by
  have hIhdr : (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  have h1 : 8 + (25 + finish) ≤ s.bytes.size := by
    rw [bytes_size] at _h; rw [bytes_size]; omega
  have hSkip := s.bytes_extract_skip_signature (25 + start) (25 + finish) h1
  rw [show (8 : Nat) + (25 + start) = 33 + start from by omega] at hSkip
  rw [show (8 : Nat) + (25 + finish) = 33 + finish from by omega] at hSkip
  rw [hSkip]
  have hExt := ByteArray.extract_append_size_add
    (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
    (b := mkChunkBytes trnsTypeBytes s.trnsWitness.payload ++
      (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
        (s.toMulti.idatChunksBytes ++
          mkChunkBytes iendTypeBytes ByteArray.empty)))
    (i := start) (j := finish)
  simpa [hIhdr] using hExt

/-- The tRNS chunk lives at byte 33, size `12 + trnsWitness.payload.size`. -/
lemma bytes_extract_trns :
    s.bytes.extract 33 (33 + 12 + s.trnsWitness.payload.size) =
      mkChunkBytes trnsTypeBytes s.trnsWitness.payload := by
  have hTrnsSize : (mkChunkBytes trnsTypeBytes s.trnsWitness.payload).size =
      12 + s.trnsWitness.payload.size := by
    rw [mkChunkBytes_size _ _ (by rfl : trnsTypeBytes.size = 4)]; omega
  have hSizeBound : 33 + (12 + s.trnsWitness.payload.size) ≤ s.bytes.size := by
    rw [bytes_size]; unfold trnsWireSize; omega
  have hSkip := s.bytes_extract_skip_through_ihdr 0 (12 + s.trnsWitness.payload.size) hSizeBound
  rw [show (33 : Nat) + 0 = 33 from rfl] at hSkip
  rw [show (33 : Nat) + (12 + s.trnsWitness.payload.size) =
      33 + 12 + s.trnsWitness.payload.size from by omega] at hSkip
  rw [hSkip]
  rw [byteArray_extract_append_prefix
    (a := mkChunkBytes trnsTypeBytes s.trnsWitness.payload)
    (b := mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (n := 12 + s.trnsWitness.payload.size) (by rw [hTrnsSize])]
  rw [show (12 + s.trnsWitness.payload.size : Nat) =
    (mkChunkBytes trnsTypeBytes s.trnsWitness.payload).size from hTrnsSize.symm]
  exact ByteArray.extract_zero_size

/-- Slicing past signature + IHDR + tRNS reveals the (bKGD ++ IDATs ++ IEND)
suffix. Starting position is `33 + (12 + trnsWitness.payload.size) =
bkgdOffset`. -/
lemma bytes_extract_skip_through_trns (start finish : Nat)
    (_h : s.bkgdOffset + finish ≤ s.bytes.size) :
    s.bytes.extract (s.bkgdOffset + start) (s.bkgdOffset + finish) =
      (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
        (s.toMulti.idatChunksBytes ++
          mkChunkBytes iendTypeBytes ByteArray.empty)).extract
        start finish := by
  have hTrnsSize : (mkChunkBytes trnsTypeBytes s.trnsWitness.payload).size =
      12 + s.trnsWitness.payload.size := by
    rw [mkChunkBytes_size _ _ (by rfl : trnsTypeBytes.size = 4)]; omega
  have hOffsetEq : s.bkgdOffset = 33 + (12 + s.trnsWitness.payload.size) := by
    unfold bkgdOffset trnsWireSize; omega
  have h1 : 33 + ((12 + s.trnsWitness.payload.size) + finish) ≤ s.bytes.size := by
    rw [hOffsetEq] at _h; omega
  have hSkip := s.bytes_extract_skip_through_ihdr ((12 + s.trnsWitness.payload.size) + start)
    ((12 + s.trnsWitness.payload.size) + finish) h1
  rw [show (33 : Nat) + ((12 + s.trnsWitness.payload.size) + start) =
      s.bkgdOffset + start from by rw [hOffsetEq]; omega] at hSkip
  rw [show (33 : Nat) + ((12 + s.trnsWitness.payload.size) + finish) =
      s.bkgdOffset + finish from by rw [hOffsetEq]; omega] at hSkip
  rw [hSkip]
  have hExt := ByteArray.extract_append_size_add
    (a := mkChunkBytes trnsTypeBytes s.trnsWitness.payload)
    (b := mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (i := start) (j := finish)
  simpa [hTrnsSize] using hExt

/-- The bKGD chunk lives at `bkgdOffset`, size `12 + bkgdWitness.payload.size`. -/
lemma bytes_extract_bkgd :
    s.bytes.extract s.bkgdOffset (s.bkgdOffset + 12 + s.bkgdWitness.payload.size) =
      mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload := by
  have hBkgdSize : (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload).size =
      12 + s.bkgdWitness.payload.size := by
    rw [mkChunkBytes_size _ _ (by rfl : bkgdTypeBytes.size = 4)]; omega
  have hSizeBound : s.bkgdOffset + (12 + s.bkgdWitness.payload.size) ≤ s.bytes.size := by
    rw [bytes_size]; unfold bkgdOffset trnsWireSize bkgdWireSize; omega
  have hSkip := s.bytes_extract_skip_through_trns 0 (12 + s.bkgdWitness.payload.size) hSizeBound
  rw [show s.bkgdOffset + 0 = s.bkgdOffset from rfl] at hSkip
  rw [show s.bkgdOffset + (12 + s.bkgdWitness.payload.size) =
      s.bkgdOffset + 12 + s.bkgdWitness.payload.size from by omega] at hSkip
  rw [hSkip]
  rw [byteArray_extract_append_prefix
    (a := mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (n := 12 + s.bkgdWitness.payload.size) (by rw [hBkgdSize])]
  rw [show (12 + s.bkgdWitness.payload.size : Nat) =
    (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload).size from hBkgdSize.symm]
  exact ByteArray.extract_zero_size

/-- Slicing past signature + IHDR + tRNS + bKGD reveals the (IDATs ++ IEND)
suffix. -/
lemma bytes_extract_skip_through_bkgd (start finish : Nat)
    (_h : s.firstIdatOffset + finish ≤ s.bytes.size) :
    s.bytes.extract (s.firstIdatOffset + start) (s.firstIdatOffset + finish) =
      (s.toMulti.idatChunksBytes ++
        mkChunkBytes iendTypeBytes ByteArray.empty).extract start finish := by
  have hBkgdSize : (mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload).size =
      12 + s.bkgdWitness.payload.size := by
    rw [mkChunkBytes_size _ _ (by rfl : bkgdTypeBytes.size = 4)]; omega
  have hOffsetEq : s.firstIdatOffset = s.bkgdOffset + (12 + s.bkgdWitness.payload.size) := by
    unfold firstIdatOffset bkgdWireSize; omega
  have h1 : s.bkgdOffset + ((12 + s.bkgdWitness.payload.size) + finish) ≤ s.bytes.size := by
    rw [hOffsetEq] at _h; omega
  have hSkip := s.bytes_extract_skip_through_trns ((12 + s.bkgdWitness.payload.size) + start)
    ((12 + s.bkgdWitness.payload.size) + finish) h1
  rw [show s.bkgdOffset + ((12 + s.bkgdWitness.payload.size) + start) =
      s.firstIdatOffset + start from by rw [hOffsetEq]; omega] at hSkip
  rw [show s.bkgdOffset + ((12 + s.bkgdWitness.payload.size) + finish) =
      s.firstIdatOffset + finish from by rw [hOffsetEq]; omega] at hSkip
  rw [hSkip]
  have hExt := ByteArray.extract_append_size_add
    (a := mkChunkBytes bkgdTypeBytes s.bkgdWitness.payload)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  simpa [hBkgdSize] using hExt

lemma bytes_extract_idat_at (i : Nat) (h : i < s.idatChunks.length) :
    s.bytes.extract (s.idatOffset i) (s.idatOffset (i + 1)) =
      mkChunkBytes idatTypeBytes s.idatChunks[i] := by
  unfold idatOffset
  have hSizeBound :
      s.firstIdatOffset +
        MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤ s.bytes.size := by
    rw [bytes_size]
    unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  rw [s.bytes_extract_skip_through_bkgd
    (MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i)
    (MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1)) hSizeBound]
  have hWithinIdat :
      MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤
        s.toMulti.idatChunksBytes.size := by
    rw [show s.toMulti.idatChunksBytes.size =
        MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length from ?_]
    · exact MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
        s.idatChunks.length (by omega)
    · rw [MultiIdatContainerSpec.idatChunksBytes_size]
      show s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 =
        MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length
      unfold MultiIdatContainerSpec.idatPrefixWireSize
      rw [List.take_length]
  rw [byteArray_extract_append_left
    (a := s.toMulti.idatChunksBytes)
    (b := mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i)
    (j := MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1))
    (Nat.le_trans (MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks i (i + 1) (by omega))
      hWithinIdat)
    hWithinIdat]
  show (s.toMulti.idatChunksBytes).extract _ _ = _
  exact s.toMulti.idatChunksBytes_extract_at i h

lemma bytes_extract_iend :
    s.bytes.extract s.iendOffset (s.iendOffset + 12) =
      mkChunkBytes iendTypeBytes ByteArray.empty := by
  unfold iendOffset
  have hSizeBound :
      s.firstIdatOffset + (s.toMulti.idatTotalWireSize + 12) ≤ s.bytes.size := by
    rw [bytes_size]
    unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
    omega
  have hSkip := s.bytes_extract_skip_through_bkgd s.toMulti.idatTotalWireSize
    (s.toMulti.idatTotalWireSize + 12) hSizeBound
  rw [show (s.firstIdatOffset + s.toMulti.idatTotalWireSize + 12 : Nat) =
      s.firstIdatOffset + (s.toMulti.idatTotalWireSize + 12) from by omega]
  rw [hSkip]
  have hIdatBytesSize :
      s.toMulti.idatChunksBytes.size = s.toMulti.idatTotalWireSize := by
    rw [MultiIdatContainerSpec.idatChunksBytes_size]
    unfold MultiIdatContainerSpec.idatTotalWireSize
    show s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 =
      MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length
    unfold MultiIdatContainerSpec.idatPrefixWireSize
    rw [List.take_length]
  have hExt := ByteArray.extract_append_size_add
    (a := s.toMulti.idatChunksBytes)
    (b := mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := 0) (j := 12)
  rw [hIdatBytesSize] at hExt
  rw [show (s.toMulti.idatTotalWireSize + 0 : Nat) = s.toMulti.idatTotalWireSize from by omega] at hExt
  rw [hExt]
  have hIendSize : (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]; simp
  rw [show (12 : Nat) = (mkChunkBytes iendTypeBytes ByteArray.empty).size from hIendSize.symm]
  exact ByteArray.extract_zero_size

/-! ### readChunk lemmas -/

set_option maxHeartbeats 800000 in
lemma readChunk_g_ihdr (hLen : 8 + 3 < s.bytes.size) :
    readChunk s.bytes 8 hLen = some (ihdrTypeBytes, encodeIHDRData s.header, 33) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hSize : 8 + 12 + (encodeIHDRData s.header).size ≤ s.bytes.size := by
    rw [bytes_size, hIhdrSize]; omega
  have hIhdrFits : (encodeIHDRData s.header).size < 2 ^ 32 := by
    rw [hIhdrSize]; decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 8
    ihdrTypeBytes (encodeIHDRData s.header)
    (by rfl) hIhdrFits s.bytes_extract_ihdr hSize hLen
  rw [show 8 + 8 + (encodeIHDRData s.header).size + 4 = 33 from by rw [hIhdrSize]] at h
  exact h

set_option maxHeartbeats 800000 in
lemma readChunk_g_trns (hLen : 33 + 3 < s.bytes.size) :
    readChunk s.bytes 33 hLen =
      some (trnsTypeBytes, s.trnsWitness.payload,
        33 + 8 + s.trnsWitness.payload.size + 4) := by
  have hSize : 33 + 12 + s.trnsWitness.payload.size ≤ s.bytes.size := by
    rw [bytes_size]; unfold trnsWireSize; omega
  exact MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 33
    trnsTypeBytes s.trnsWitness.payload (by rfl) s.trnsWitness.hPayloadFits
    s.bytes_extract_trns hSize hLen

set_option maxHeartbeats 800000 in
lemma readChunk_g_bkgd (hLen : s.bkgdOffset + 3 < s.bytes.size) :
    readChunk s.bytes s.bkgdOffset hLen =
      some (bkgdTypeBytes, s.bkgdWitness.payload,
        s.bkgdOffset + 8 + s.bkgdWitness.payload.size + 4) := by
  have hSize : s.bkgdOffset + 12 + s.bkgdWitness.payload.size ≤ s.bytes.size := by
    rw [bytes_size]; unfold bkgdOffset trnsWireSize bkgdWireSize; omega
  exact MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes s.bkgdOffset
    bkgdTypeBytes s.bkgdWitness.payload (by rfl) s.bkgdWitness.hPayloadFits
    s.bytes_extract_bkgd hSize hLen

set_option maxHeartbeats 800000 in
lemma readChunk_g_idat (i : Nat) (h : i < s.idatChunks.length)
    (hLen : s.idatOffset i + 3 < s.bytes.size) :
    readChunk s.bytes (s.idatOffset i) hLen =
      some (idatTypeBytes, s.idatChunks[i],
        s.idatOffset i + 8 + s.idatChunks[i].size + 4) := by
  have hChunkSize := s.hChunkSize s.idatChunks[i] (List.getElem_mem h)
  have hChunkRangeBound :
      s.idatOffset i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    unfold idatOffset
    rw [bytes_size]
    unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
    have hStep := MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  have hWrap :
      s.bytes.extract (s.idatOffset i) (s.idatOffset i + 12 + s.idatChunks[i].size) =
        mkChunkBytes idatTypeBytes s.idatChunks[i] := by
    have hWidth :
        s.idatOffset (i + 1) = s.idatOffset i + 12 + s.idatChunks[i].size := by
      unfold idatOffset
      rw [MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h]
      omega
    have hExt := s.bytes_extract_idat_at i h
    rw [← hWidth]; exact hExt
  exact MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes (s.idatOffset i)
    idatTypeBytes s.idatChunks[i] (by rfl) hChunkSize hWrap hChunkRangeBound hLen

set_option maxHeartbeats 800000 in
lemma readChunk_g_iend (hLen : s.iendOffset + 3 < s.bytes.size) :
    readChunk s.bytes s.iendOffset hLen =
      some (iendTypeBytes, ByteArray.empty, s.bytes.size) := by
  have hSize : s.iendOffset + 12 + ByteArray.empty.size ≤ s.bytes.size := by
    unfold iendOffset
    rw [bytes_size]
    unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
    simp; omega
  have hEmptyFits : (ByteArray.empty : ByteArray).size < 2 ^ 32 := by decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes s.iendOffset
    iendTypeBytes ByteArray.empty (by rfl) hEmptyFits s.bytes_extract_iend hSize hLen
  rw [show s.iendOffset + 8 + ByteArray.empty.size + 4 = s.bytes.size from ?_] at h
  · exact h
  · unfold iendOffset
    rw [bytes_size]
    unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
    simp; omega

/-! ### Walk lemmas -/

/-- State after processing the first `i` IDAT chunks (with the full
expected metadata already populated). -/
private def stateAfterIdats (i : Nat) : PngMetadataParseState :=
  { header := some s.header
    idat := s.idatChunks.take i |>.foldl (· ++ ·) ByteArray.empty
    seenPLTE := false
    seenIDAT := 0 < i
    closedIDAT := false
    metadata := s.expectedMetadata }

private lemma stateAfterIdats_idat_full :
    (s.stateAfterIdats s.idatChunks.length).idat = s.idatData := by
  unfold stateAfterIdats idatData MultiIdatContainerSpec.idatData toMulti
  rw [List.take_length]

private lemma stateAfterIdats_idat_succ (i : Nat) (h : i < s.idatChunks.length) :
    (s.stateAfterIdats (i + 1)).idat =
      (s.stateAfterIdats i).idat ++ s.idatChunks[i] := by
  unfold stateAfterIdats
  show (s.idatChunks.take (i + 1)).foldl (· ++ ·) ByteArray.empty =
    (s.idatChunks.take i).foldl (· ++ ·) ByteArray.empty ++ s.idatChunks[i]
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp [List.foldl]

set_option maxHeartbeats 1200000 in
lemma walk_idat_step (i : Nat) (h : i < s.idatChunks.length) (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffset (i + 1))
              (s.stateAfterIdats (i + 1)) =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes (s.idatOffset i)
        (s.stateAfterIdats i) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hChunkRangeBound :
      s.idatOffset i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    unfold idatOffset
    rw [bytes_size]
    unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
    have hStep := MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  have hLen : s.idatOffset i + 3 < s.bytes.size := by omega
  have hPos : s.idatOffset i + 8 ≤ s.bytes.size := by omega
  have hReadIdat := s.readChunk_g_idat i h hLen
  have hNextOffsetEq :
      s.idatOffset i + 8 + s.idatChunks[i].size + 4 = s.idatOffset (i + 1) := by
    unfold idatOffset
    rw [MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h]
    omega
  rw [hNextOffsetEq] at hReadIdat
  have hStep := parsePngLoopFuelWithMetadata_idat_appends_when_open fuel s.bytes
    (s.idatOffset i) (s.stateAfterIdats i) s.header idatTypeBytes
    s.idatChunks[i] (s.idatOffset (i + 1))
    hPos hLen hReadIdat
    (by unfold stateAfterIdats; rfl)
    (by decide) (by decide) (by decide)
    (by unfold stateAfterIdats; rfl)
    (by
      unfold stateAfterIdats
      simp
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide)
  rw [hStep]
  have hIdatEq : (s.stateAfterIdats i).idat ++ s.idatChunks[i] =
      (s.stateAfterIdats (i + 1)).idat := by
    rw [s.stateAfterIdats_idat_succ i h]
  have hStateEq :
      ({ header := some s.header
         idat := (s.stateAfterIdats i).idat ++ s.idatChunks[i]
         seenPLTE := (s.stateAfterIdats i).seenPLTE
         seenIDAT := true
         closedIDAT := false
         metadata := (s.stateAfterIdats i).metadata : PngMetadataParseState }) =
      s.stateAfterIdats (i + 1) := by
    rw [hIdatEq]
    unfold stateAfterIdats
    rfl
  rw [hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
lemma walk_idats_aux (i : Nat) (hi : i ≤ s.idatChunks.length)
    (fuel : Nat) (hFuel : s.idatChunks.length - i + 1 ≤ fuel) :
    parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffset i)
      (s.stateAfterIdats i) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  induction h : s.idatChunks.length - i generalizing i fuel with
  | zero =>
      have hin : i = s.idatChunks.length := by omega
      cases fuel with
      | zero => rw [hin] at hFuel; simp at hFuel
      | succ fuel' =>
          have hOffsetEq : s.idatOffset i = s.iendOffset := by
            unfold idatOffset iendOffset MultiIdatContainerSpec.idatTotalWireSize
            rw [hin]
            rfl
          rw [hOffsetEq]
          have hLen : s.iendOffset + 3 < s.bytes.size := by
            unfold iendOffset
            rw [bytes_size]
            unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
            omega
          have hPos : s.iendOffset + 8 ≤ s.bytes.size := by
            unfold iendOffset
            rw [bytes_size]
            unfold firstIdatOffset bkgdOffset trnsWireSize bkgdWireSize
            omega
          have hReadIend := s.readChunk_g_iend hLen
          have hSeenIDAT : (s.stateAfterIdats i).seenIDAT = true := by
            unfold stateAfterIdats
            simp
            rw [hin]
            cases hChunks : s.idatChunks with
            | nil => exact absurd hChunks s.hNonempty
            | cons _ _ => simp
          have hHeader : (s.stateAfterIdats i).header = some s.header := rfl
          have hIdatEq : (s.stateAfterIdats i).idat = s.idatData := by
            rw [hin]; exact s.stateAfterIdats_idat_full
          have hMetaEq :
              (s.stateAfterIdats i).metadata = s.expectedMetadata := rfl
          have hRes :=
            MultiIdatContainerSpec.parsePngLoopFuelWithMetadata_iend_success_step
              fuel' s.bytes s.iendOffset (s.stateAfterIdats i) s.header
              hPos hLen hReadIend hHeader hSeenIDAT
          rw [hIdatEq, hMetaEq] at hRes
          exact hRes
  | succ k ih =>
      have hilt : i < s.idatChunks.length := by omega
      cases fuel with
      | zero => have : s.idatChunks.length - i + 1 ≤ 0 := hFuel; omega
      | succ fuel' =>
          have hi' : i + 1 ≤ s.idatChunks.length := by omega
          have hk' : s.idatChunks.length - (i + 1) = k := by omega
          have hFuel' : s.idatChunks.length - (i + 1) + 1 ≤ fuel' := by
            have hkfuel : s.idatChunks.length - i + 1 ≤ fuel' + 1 := hFuel
            omega
          have hRest := ih (i := i + 1) hi' fuel' hFuel' hk'
          exact s.walk_idat_step i hilt fuel' hRest

/-- State just before processing bKGD: tRNS metadata already populated,
background not yet set. -/
private def stateBeforeBkgd : PngMetadataParseState :=
  { header := some s.header
    idat := ByteArray.empty
    seenPLTE := false
    seenIDAT := false
    closedIDAT := false
    metadata := { PngMetadata.empty with transparency := some s.trnsWitness.trns } }

set_option maxHeartbeats 1200000 in
lemma walk_bkgd_step (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffset 0)
              (s.stateAfterIdats 0) =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes s.bkgdOffset
        s.stateBeforeBkgd =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : s.bkgdOffset + 8 ≤ s.bytes.size := by
    rw [bytes_size]; unfold bkgdOffset trnsWireSize bkgdWireSize; omega
  have hLen : s.bkgdOffset + 3 < s.bytes.size := by
    rw [bytes_size]; unfold bkgdOffset trnsWireSize bkgdWireSize; omega
  have hReadBkgd := s.readChunk_g_bkgd hLen
  have hNotIHDR : (bkgdTypeBytes == ihdrTypeBytes) = false := by decide
  have hNotPLTE : (bkgdTypeBytes == plteTypeBytes) = false := by decide
  have hNotIDAT : (bkgdTypeBytes == idatTypeBytes) = false := by decide
  have hNotIEND : (bkgdTypeBytes == iendTypeBytes) = false := by decide
  have hNotTRNS : (bkgdTypeBytes == trnsTypeBytes) = false := by decide
  have hIsBKGD : (bkgdTypeBytes == bkgdTypeBytes) = true := by decide
  have hHeader : s.stateBeforeBkgd.header = some s.header := rfl
  have hSeenIDAT : s.stateBeforeBkgd.seenIDAT = false := rfl
  have hDup : s.stateBeforeBkgd.metadata.background.isSome = false := by
    unfold stateBeforeBkgd; rfl
  have hStep := parsePngLoopFuelWithMetadata_accepts_bKGD fuel s.bytes s.bkgdOffset
    s.stateBeforeBkgd s.header bkgdTypeBytes s.bkgdWitness.payload
    (s.bkgdOffset + 8 + s.bkgdWitness.payload.size + 4) s.bkgdWitness.bkgd
    hPos hLen hReadBkgd hHeader
    hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS
    hIsBKGD hSeenIDAT hDup s.bkgdWitness.hParses
  rw [hStep]
  -- The resulting state: stateBeforeBkgd with metadata.background := some bkgd.
  -- Next position is firstIdatOffset == idatOffset 0.
  have hOffsetEq :
      s.bkgdOffset + 8 + s.bkgdWitness.payload.size + 4 = s.idatOffset 0 := by
    unfold idatOffset firstIdatOffset bkgdWireSize
    unfold MultiIdatContainerSpec.idatPrefixWireSize
    simp
    omega
  have hStateEq :
      ({ s.stateBeforeBkgd with metadata :=
            { s.stateBeforeBkgd.metadata with background := some s.bkgdWitness.bkgd } }
        : PngMetadataParseState) =
      s.stateAfterIdats 0 := by
    unfold stateBeforeBkgd stateAfterIdats expectedMetadata
    simp [List.foldl]
  rw [hOffsetEq, hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
lemma walk_trns_step (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes s.bkgdOffset
              s.stateBeforeBkgd =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 33
        { header := some s.header, idat := ByteArray.empty,
          seenPLTE := false, seenIDAT := false, closedIDAT := false,
          metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (33 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size]; unfold trnsWireSize; omega
  have hLen : (33 : Nat) + 3 < s.bytes.size := by
    rw [bytes_size]; unfold trnsWireSize; omega
  have hReadTrns := s.readChunk_g_trns hLen
  have hNotIHDR : (trnsTypeBytes == ihdrTypeBytes) = false := by decide
  have hNotPLTE : (trnsTypeBytes == plteTypeBytes) = false := by decide
  have hNotIDAT : (trnsTypeBytes == idatTypeBytes) = false := by decide
  have hNotIEND : (trnsTypeBytes == iendTypeBytes) = false := by decide
  have hIsTRNS : (trnsTypeBytes == trnsTypeBytes) = true := by decide
  have hStep := parsePngLoopFuelWithMetadata_accepts_tRNS fuel s.bytes 33
    ({ header := some s.header, idat := ByteArray.empty,
       seenPLTE := false, seenIDAT := false, closedIDAT := false,
       metadata := PngMetadata.empty } : PngMetadataParseState)
    s.header trnsTypeBytes s.trnsWitness.payload
    (33 + 8 + s.trnsWitness.payload.size + 4) s.trnsWitness.trns
    hPos hLen hReadTrns rfl
    hNotIHDR hNotPLTE hNotIDAT hNotIEND
    hIsTRNS rfl rfl s.trnsWitness.hParses
  rw [hStep]
  -- After tRNS step, the next position is bkgdOffset and the state matches
  -- stateBeforeBkgd.
  have hOffsetEq : (33 + 8 + s.trnsWitness.payload.size + 4 : Nat) = s.bkgdOffset := by
    unfold bkgdOffset trnsWireSize
    omega
  have hStateEq :
      ({ ({ header := some s.header, idat := ByteArray.empty,
            seenPLTE := false, seenIDAT := false, closedIDAT := false,
            metadata := PngMetadata.empty } : PngMetadataParseState) with
          metadata :=
            { (PngMetadata.empty) with transparency := some s.trnsWitness.trns } }
        : PngMetadataParseState) =
      s.stateBeforeBkgd := by
    unfold stateBeforeBkgd
    rfl
  rw [hOffsetEq, hStateEq]
  exact hRest

set_option maxHeartbeats 1600000 in
lemma walk_ihdr_step (fuel : Nat)
    (hFuel : s.idatChunks.length + 3 ≤ fuel) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (8 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size]; unfold trnsWireSize; omega
  have hLen : (8 : Nat) + 3 < s.bytes.size := by
    rw [bytes_size]; unfold trnsWireSize; omega
  have hReadIhdr := s.readChunk_g_ihdr hLen
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hCT256 : s.header.colorType < 256 := by
    rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
  have hBDlt : s.header.bitDepth < 256 := by
    rcases s.hBitDepth with h | h | h <;> rw [h] <;> decide
  have hParseHdr := parseIHDRData_encodeIHDRData_lt256 s.header
    s.hWidth s.hHeight hBDlt s.hInterlace hCT256
  conv => lhs; unfold parsePngLoopFuelWithMetadata
  have hReadU32Len : readU32BE s.bytes 8 hLen = 13 := by
    have hExtractLen : s.bytes.extract 8 (8 + 4) = u32be 13 := by
      have h := s.bytes_extract_ihdr
      have hChunkLen :=
        MultiIdatContainerSpec.mkChunkBytes_extract_len ihdrTypeBytes
          (encodeIHDRData s.header)
      rw [hIhdrSize] at hChunkLen
      have hsub :
          (s.bytes.extract 8 (8 + 12 + (encodeIHDRData s.header).size)).extract 0 4 =
          (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).extract 0 4 := by
        rw [h]
      rw [hChunkLen] at hsub
      have hExt := ByteArray.extract_extract (a := s.bytes) (i := 8)
        (j := 8 + 12 + (encodeIHDRData s.header).size) (k := 0) (l := 4)
      have hMin : min (8 + 4) (8 + 12 + (encodeIHDRData s.header).size) = 8 + 4 := by
        rw [hIhdrSize]; omega
      rw [hMin] at hExt
      rw [← hExt]
      exact hsub
    exact readU32BE_of_extract_eq s.bytes 8 13 hLen hExtractLen (by decide)
  simp [hPos, hLen, hReadIhdr, hReadU32Len, hParseHdr]
  refine ⟨by decide, ?_⟩
  -- After the IHDR step the parser is at position 33 with the post-IHDR state.
  -- We chain walk_trns_step → walk_bkgd_step → walk_idats_aux.
  cases fuel with
  | zero => omega
  | succ fuel' =>
      -- walk_trns_step fuel' yields the goal at position 33 with fuel' + 1.
      have hWalkTrns := s.walk_trns_step fuel' ?_
      · exact hWalkTrns
      · cases fuel' with
        | zero => omega
        | succ fuel'' =>
            have hWalkBkgd := s.walk_bkgd_step fuel'' ?_
            · exact hWalkBkgd
            · -- walk_idats_aux needs idatChunks.length + 1 fuel for 0..length walk + IEND.
              exact s.walk_idats_aux 0 (by omega) fuel'' (by omega)

/-! ### Main theorem -/

set_option maxHeartbeats 1600000 in
theorem parsePngForDecode_multiIdatTrnsBkgdContainerSpec_correct
    (s : MultiIdatTrnsBkgdContainerSpec) :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  -- The simple fast-path fails because the third chunk is tRNS (not IDAT).
  have hSimpleNone : parsePngSimple s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimple
    have hSig : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
    have hLen1 : (8 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size]; unfold trnsWireSize; omega
    have hLen2 : (33 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size]; unfold trnsWireSize; omega
    have hRead1 := s.readChunk_g_ihdr hLen1
    have hRead2 := s.readChunk_g_trns hLen2
    have hCT256 : s.header.colorType < 256 := by
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
    have hBDlt : s.header.bitDepth < 256 := by
      rcases s.hBitDepth with h | h | h <;> rw [h] <;> decide
    have hParseHdr := parseIHDRData_encodeIHDRData_lt256 s.header
      s.hWidth s.hHeight hBDlt s.hInterlace hCT256
    have hCtBdOk :
        pngColorTypeBitDepthSupported s.header.colorType s.header.bitDepth = true :=
      s.hCtBdSupported
    have hNotIDAT : (trnsTypeBytes != idatTypeBytes) = true := by decide
    simp [hSig, hLen1, hRead1, hParseHdr, hCtBdOk,
          hLen2, hRead2, hNotIDAT,
          bne_self_eq_false' (a := ihdrTypeBytes)]
  have hSimpleMetaNone : parsePngSimpleWithMetadata s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimpleWithMetadata
    simp [hSimpleNone]
  have hSigExtract : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
  have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
    rw [hSigExtract]; exact bne_self_eq_false' (a := pngSignature)
  have hLoopFuel : s.idatChunks.length + 3 ≤ s.bytes.size := by
    rw [bytes_size]
    unfold trnsWireSize bkgdWireSize MultiIdatContainerSpec.idatTotalWireSize
      MultiIdatContainerSpec.idatPrefixWireSize
    rw [List.take_length]
    have hSum : 12 * s.idatChunks.length ≤
        s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 := by
      have aux : ∀ (acc : Nat) (chunks : List ByteArray),
          acc + 12 * chunks.length ≤
            chunks.foldl (fun a c => a + 12 + c.size) acc := by
        intro acc chunks
        induction chunks generalizing acc with
        | nil => simp
        | cons d ds ih =>
            simp only [List.length_cons, List.foldl_cons]
            have h := ih (acc + 12 + d.size)
            have : acc + 12 * (ds.length + 1) ≤
                acc + 12 + d.size + 12 * ds.length := by omega
            exact Nat.le_trans this h
      have h := aux 0 s.idatChunks
      simpa using h
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  unfold parsePngForDecode parsePngWithMetadata
  simp [hSimpleMetaNone, hSigCheck]
  exact s.walk_ihdr_step s.bytes.size hLoopFuel

end MultiIdatTrnsBkgdContainerSpec

end Lemmas

end Bitmaps
