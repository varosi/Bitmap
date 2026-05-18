import Bitmap.Lemmas.Png.MultiIdatContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Generic multi-IDAT container with an optional pre-IDAT ancillary chunk

`MultiIdatGenericPreChunkContainerSpec` describes a PNG byte stream with the
multi-IDAT shape plus *at most one* optional ancillary chunk placed between
IHDR and the first IDAT. Each specific chunk type (tIME, pHYs, gAMA, cHRM,
sRGB, tRNS, bKGD) is an instance of this generic spec — the chunk-specific
parsing logic is captured by a single `hAcceptStep` field that says "starting
from the post-IHDR state at position 33, walking one fuel step advances by
`12 + payload.size` bytes and produces the expected metadata".

This abstraction eliminates the duplication that would otherwise force a
separate ~900-line file per chunk type. The bytes layout, position
arithmetic, per-chunk `readChunk` lemmas, and inductive `walk` lemmas are
all proven once over the generic spec; each specific instantiation supplies
only the chunk's type bytes, payload, and packaged step witness. -/

/-- A "pre-IDAT chunk" witness: the chunk's type bytes (4 bytes), its
payload, and an `hAcceptStep` field certifying that the metadata-aware
parser walks past this chunk in one fuel step. The witness is parameterised
by the surrounding PNG header so that chunk types whose validity depends
on `colorType` (`tRNS`, `bKGD`) can be expressed. -/
structure PreIdatChunk (hdr : PngHeader) where
  /-- The chunk's 4-byte type identifier (e.g., `timeTypeBytes`). -/
  typeBytes : ByteArray
  /-- Size constraint on the type identifier. -/
  hTypeSize : typeBytes.size = 4
  /-- The chunk type is not `IDAT` (so `parsePngSimple`'s fast path rejects). -/
  hTypeNotIDAT : (typeBytes == idatTypeBytes) = false
  /-- The chunk type is not `IHDR` (so the metadata-aware parser doesn't
  re-enter the IHDR branch on the second chunk read). -/
  hTypeNotIHDR : (typeBytes == ihdrTypeBytes) = false
  /-- The chunk's raw payload bytes. -/
  payload : ByteArray
  /-- The payload fits in the PNG u32 length field. -/
  hPayloadFits : payload.size < 2 ^ 32
  /-- The metadata this chunk produces when parsed in isolation. -/
  expectedMetadata : PngMetadata
  /-- The packaged walk-step witness. -/
  hAcceptStep : ∀ (fuel : Nat) (bytes : ByteArray) (pos : Nat)
                (state : PngMetadataParseState)
                (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
                (hread : readChunk bytes pos hLen =
                  some (typeBytes, payload, pos + 8 + payload.size + 4))
                (hheader : state.header = some hdr)
                (hPLTE : state.seenPLTE = false)
                (hIDAT : state.seenIDAT = false)
                (hClosed : state.closedIDAT = false)
                (hMetaEmpty : state.metadata = PngMetadata.empty),
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
    parsePngLoopFuelWithMetadata fuel bytes (pos + 8 + payload.size + 4)
      { header := state.header
        idat := state.idat
        seenPLTE := state.seenPLTE
        seenIDAT := state.seenIDAT
        closedIDAT := state.closedIDAT
        metadata := expectedMetadata }

/-- A PNG byte stream with the multi-IDAT shape plus an optional pre-IDAT
ancillary chunk. -/
structure MultiIdatGenericPreChunkContainerSpec where
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
  /-- Optional pre-IDAT ancillary chunk. -/
  preChunk : Option (PreIdatChunk header)

namespace MultiIdatGenericPreChunkContainerSpec

variable (s : MultiIdatGenericPreChunkContainerSpec)

/-- The underlying multi-IDAT spec (forgetting the pre-chunk). -/
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

/-- The wrapped pre-chunk bytes (`mkChunkBytes typeBytes payload` if some,
empty otherwise). -/
def preChunkBytes : ByteArray :=
  match s.preChunk with
  | none => ByteArray.empty
  | some w => mkChunkBytes w.typeBytes w.payload

/-- Wire size of the pre-chunk: `12 + payload.size` when present, 0 otherwise. -/
def preChunkWireSize : Nat :=
  match s.preChunk with
  | none => 0
  | some w => 12 + w.payload.size

/-- The byte layout: signature, IHDR, optional pre-chunk, IDATs, IEND. -/
def bytes : ByteArray :=
  pngSignature ++
  mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
  s.preChunkBytes ++
  s.toMulti.idatChunksBytes ++
  mkChunkBytes iendTypeBytes ByteArray.empty

/-- The concatenated IDAT payload — same as the underlying multi-IDAT. -/
def idatData : ByteArray :=
  s.toMulti.idatData

/-- The metadata produced by parsing this byte stream. -/
def expectedMetadata : PngMetadata :=
  match s.preChunk with
  | none => PngMetadata.empty
  | some w => w.expectedMetadata


/-! ### Wire-size helpers -/

lemma preChunkWireSize_of_none (h : s.preChunk = none) :
    s.preChunkWireSize = 0 := by
  unfold preChunkWireSize; rw [h]

lemma preChunkWireSize_of_some {w : PreIdatChunk s.header} (h : s.preChunk = some w) :
    s.preChunkWireSize = 12 + w.payload.size := by
  unfold preChunkWireSize; rw [h]

lemma preChunkBytes_size_of_some {w : PreIdatChunk s.header} (h : s.preChunk = some w) :
    s.preChunkBytes.size = 12 + w.payload.size := by
  unfold preChunkBytes
  rw [h]
  rw [mkChunkBytes_size w.typeBytes w.payload w.hTypeSize]
  omega

lemma preChunkBytes_size : s.preChunkBytes.size = s.preChunkWireSize := by
  unfold preChunkWireSize
  match h : s.preChunk with
  | none => unfold preChunkBytes; rw [h]; simp
  | some w => rw [s.preChunkBytes_size_of_some h]

/-! ### Bytes size -/

lemma bytes_size :
    s.bytes.size =
      45 + s.preChunkWireSize + s.toMulti.idatTotalWireSize := by
  unfold bytes
  have hIhdrSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  have hIendSize :
      (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]; simp
  have hPreSize : s.preChunkBytes.size = s.preChunkWireSize := s.preChunkBytes_size
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
      ByteArray.size_append, pngSignature_size, hIhdrSize, hPreSize,
      hIdatSize, hIendSize]
  omega

lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := by
  rw [bytes_size]; omega

/-! ### Position arithmetic -/

def idatOffset (i : Nat) : Nat :=
  33 + s.preChunkWireSize + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i

def iendOffset : Nat :=
  33 + s.preChunkWireSize + s.toMulti.idatTotalWireSize

/-! ### Bytes-extract lemmas -/

lemma bytes_eq_signature_then_rest :
    s.bytes =
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (s.preChunkBytes ++
            (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))) := by
  unfold bytes
  simp [ByteArray.append_assoc]

lemma bytes_extract_signature : s.bytes.extract 0 8 = pngSignature := by
  rw [s.bytes_eq_signature_then_rest]
  have hSig : pngSignature.size = 8 := pngSignature_size
  rw [byteArray_extract_append_prefix
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (s.preChunkBytes ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)))
    (n := 8) (by simp [hSig])]
  rw [← hSig]
  exact ByteArray.extract_zero_size

lemma bytes_extract_skip_signature (start finish : Nat)
    (_h : 8 + finish ≤ s.bytes.size) :
    s.bytes.extract (8 + start) (8 + finish) =
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        (s.preChunkBytes ++
          (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))).extract
        start finish := by
  rw [s.bytes_eq_signature_then_rest]
  have hSig : pngSignature.size = 8 := pngSignature_size
  have h' := ByteArray.extract_append_size_add
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (s.preChunkBytes ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)))
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
    (b := s.preChunkBytes ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (n := 25) (by rw [hIhdrChunkSize])]
  rw [show (25 : Nat) = (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size from
    hIhdrChunkSize.symm]
  exact ByteArray.extract_zero_size

lemma bytes_extract_skip_through_ihdr (start finish : Nat)
    (_h : 33 + finish ≤ s.bytes.size) :
    s.bytes.extract (33 + start) (33 + finish) =
      (s.preChunkBytes ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)).extract
        start finish := by
  have hSig : pngSignature.size = 8 := pngSignature_size
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
    (b := s.preChunkBytes ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (i := start) (j := finish)
  simpa [hIhdr] using hExt

/-- The pre-chunk lives at byte 33 (when present), with size
`12 + w.payload.size`. -/
lemma bytes_extract_preChunk {w : PreIdatChunk s.header} (hw : s.preChunk = some w) :
    s.bytes.extract 33 (33 + 12 + w.payload.size) =
      mkChunkBytes w.typeBytes w.payload := by
  have hPreSize : s.preChunkBytes.size = 12 + w.payload.size :=
    s.preChunkBytes_size_of_some hw
  have hSizeBound : 33 + (12 + w.payload.size) ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
  have hSkip := s.bytes_extract_skip_through_ihdr 0 (12 + w.payload.size) hSizeBound
  rw [show (33 : Nat) + 0 = 33 from rfl] at hSkip
  rw [show (33 : Nat) + (12 + w.payload.size) = 33 + 12 + w.payload.size from by omega] at hSkip
  rw [hSkip]
  rw [byteArray_extract_append_prefix
    (a := s.preChunkBytes)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (n := 12 + w.payload.size) (by rw [hPreSize])]
  rw [show (12 + w.payload.size : Nat) = s.preChunkBytes.size from hPreSize.symm]
  rw [ByteArray.extract_zero_size]
  unfold preChunkBytes
  rw [hw]

/-- Slicing past signature + IHDR + pre-chunk reveals the
(IDATs ++ IEND) suffix. The starting position is
`33 + (12 + w.payload.size) = 45 + w.payload.size` for the some case. -/
lemma bytes_extract_skip_through_preChunk {w : PreIdatChunk s.header}
    (hw : s.preChunk = some w) (start finish : Nat)
    (_h : 45 + w.payload.size + finish ≤ s.bytes.size) :
    s.bytes.extract (45 + w.payload.size + start) (45 + w.payload.size + finish) =
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty).extract
        start finish := by
  have hPreSize : s.preChunkBytes.size = 12 + w.payload.size :=
    s.preChunkBytes_size_of_some hw
  have h1 : 33 + ((12 + w.payload.size) + finish) ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw] at _h
    rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
  have hSkip := s.bytes_extract_skip_through_ihdr ((12 + w.payload.size) + start)
    ((12 + w.payload.size) + finish) h1
  rw [show (33 : Nat) + ((12 + w.payload.size) + start) =
      45 + w.payload.size + start from by omega] at hSkip
  rw [show (33 : Nat) + ((12 + w.payload.size) + finish) =
      45 + w.payload.size + finish from by omega] at hSkip
  rw [hSkip]
  have hExt := ByteArray.extract_append_size_add
    (a := s.preChunkBytes)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  simpa [hPreSize] using hExt

lemma bytes_extract_idat_at {w : PreIdatChunk s.header} (hw : s.preChunk = some w)
    (i : Nat) (h : i < s.idatChunks.length) :
    s.bytes.extract (s.idatOffset i) (s.idatOffset (i + 1)) =
      mkChunkBytes idatTypeBytes s.idatChunks[i] := by
  unfold idatOffset
  rw [s.preChunkWireSize_of_some hw]
  rw [show (33 : Nat) + (12 + w.payload.size) +
      MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i =
      45 + w.payload.size + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i from by omega]
  rw [show (33 : Nat) + (12 + w.payload.size) +
      MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) =
      45 + w.payload.size + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) from by
      omega]
  have hSizeBound :
      45 + w.payload.size +
        MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw]
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  rw [s.bytes_extract_skip_through_preChunk hw
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

lemma bytes_extract_iend {w : PreIdatChunk s.header} (hw : s.preChunk = some w) :
    s.bytes.extract s.iendOffset (s.iendOffset + 12) =
      mkChunkBytes iendTypeBytes ByteArray.empty := by
  unfold iendOffset
  rw [s.preChunkWireSize_of_some hw]
  rw [show (33 : Nat) + (12 + w.payload.size) + s.toMulti.idatTotalWireSize =
      45 + w.payload.size + s.toMulti.idatTotalWireSize from by omega]
  have hSizeBound :
      45 + w.payload.size + (s.toMulti.idatTotalWireSize + 12) ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
  have hSkip := s.bytes_extract_skip_through_preChunk hw s.toMulti.idatTotalWireSize
    (s.toMulti.idatTotalWireSize + 12) hSizeBound
  rw [show (45 + w.payload.size + s.toMulti.idatTotalWireSize + 12 : Nat) =
      45 + w.payload.size + (s.toMulti.idatTotalWireSize + 12) from by omega]
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
lemma readChunk_g_ihdr {w : PreIdatChunk s.header} (hw : s.preChunk = some w)
    (hLen : 8 + 3 < s.bytes.size) :
    readChunk s.bytes 8 hLen = some (ihdrTypeBytes, encodeIHDRData s.header, 33) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hSize : 8 + 12 + (encodeIHDRData s.header).size ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw, hIhdrSize]; omega
  have hIhdrFits : (encodeIHDRData s.header).size < 2 ^ 32 := by
    rw [hIhdrSize]; decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 8
    ihdrTypeBytes (encodeIHDRData s.header)
    (by rfl) hIhdrFits s.bytes_extract_ihdr hSize hLen
  rw [show 8 + 8 + (encodeIHDRData s.header).size + 4 = 33 from by rw [hIhdrSize]] at h
  exact h

set_option maxHeartbeats 800000 in
lemma readChunk_g_preChunk {w : PreIdatChunk s.header} (hw : s.preChunk = some w)
    (hLen : 33 + 3 < s.bytes.size) :
    readChunk s.bytes 33 hLen =
      some (w.typeBytes, w.payload, 33 + 8 + w.payload.size + 4) := by
  have hSize : 33 + 12 + w.payload.size ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
  exact MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 33
    w.typeBytes w.payload w.hTypeSize w.hPayloadFits (s.bytes_extract_preChunk hw) hSize hLen

set_option maxHeartbeats 800000 in
lemma readChunk_g_idat {w : PreIdatChunk s.header} (hw : s.preChunk = some w) (i : Nat)
    (h : i < s.idatChunks.length)
    (hLen : s.idatOffset i + 3 < s.bytes.size) :
    readChunk s.bytes (s.idatOffset i) hLen =
      some (idatTypeBytes, s.idatChunks[i],
        s.idatOffset i + 8 + s.idatChunks[i].size + 4) := by
  have hChunkSize := s.hChunkSize s.idatChunks[i] (List.getElem_mem h)
  have hChunkRangeBound :
      s.idatOffset i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    unfold idatOffset
    rw [bytes_size, s.preChunkWireSize_of_some hw]
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
    have hExt := s.bytes_extract_idat_at hw i h
    rw [← hWidth]; exact hExt
  exact MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes (s.idatOffset i)
    idatTypeBytes s.idatChunks[i] (by rfl) hChunkSize hWrap hChunkRangeBound hLen

set_option maxHeartbeats 800000 in
lemma readChunk_g_iend {w : PreIdatChunk s.header} (hw : s.preChunk = some w)
    (hLen : s.iendOffset + 3 < s.bytes.size) :
    readChunk s.bytes s.iendOffset hLen =
      some (iendTypeBytes, ByteArray.empty, s.bytes.size) := by
  have hSize : s.iendOffset + 12 + ByteArray.empty.size ≤ s.bytes.size := by
    unfold iendOffset
    rw [bytes_size, s.preChunkWireSize_of_some hw]
    simp; omega
  have hEmptyFits : (ByteArray.empty : ByteArray).size < 2 ^ 32 := by decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes s.iendOffset
    iendTypeBytes ByteArray.empty (by rfl) hEmptyFits (s.bytes_extract_iend hw) hSize hLen
  rw [show s.iendOffset + 8 + ByteArray.empty.size + 4 = s.bytes.size from ?_] at h
  · exact h
  · unfold iendOffset
    rw [bytes_size, s.preChunkWireSize_of_some hw]
    simp; omega

/-! ### Walk lemmas -/

/-- State after processing the first `i` IDAT chunks (in the pre-chunk variant). -/
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
lemma walk_idat_step {w : PreIdatChunk s.header} (hw : s.preChunk = some w) (i : Nat)
    (h : i < s.idatChunks.length)
    (fuel : Nat)
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
    rw [bytes_size, s.preChunkWireSize_of_some hw]
    have hStep := MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  have hLen : s.idatOffset i + 3 < s.bytes.size := by omega
  have hPos : s.idatOffset i + 8 ≤ s.bytes.size := by omega
  have hReadIdat := s.readChunk_g_idat hw i h hLen
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
lemma walk_idats_aux {w : PreIdatChunk s.header} (hw : s.preChunk = some w)
    (i : Nat) (hi : i ≤ s.idatChunks.length)
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
            rw [bytes_size, s.preChunkWireSize_of_some hw]
            omega
          have hPos : s.iendOffset + 8 ≤ s.bytes.size := by
            unfold iendOffset
            rw [bytes_size, s.preChunkWireSize_of_some hw]
            omega
          have hReadIend := s.readChunk_g_iend hw hLen
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
          exact s.walk_idat_step hw i hilt fuel' hRest

set_option maxHeartbeats 1200000 in
lemma walk_preChunk_step {w : PreIdatChunk s.header} (hw : s.preChunk = some w)
    (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffset 0)
              (s.stateAfterIdats 0) =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 33
        { header := some s.header, idat := ByteArray.empty,
          seenPLTE := false, seenIDAT := false, closedIDAT := false,
          metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (33 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
  have hLen : (33 : Nat) + 3 < s.bytes.size := by omega
  have hReadPre := s.readChunk_g_preChunk hw hLen
  -- Apply the chunk's accept-step witness.
  have hStep := w.hAcceptStep fuel s.bytes 33
    { header := some s.header, idat := ByteArray.empty,
      seenPLTE := false, seenIDAT := false, closedIDAT := false,
      metadata := PngMetadata.empty } hPos hLen hReadPre rfl rfl rfl rfl rfl
  rw [hStep]
  -- The new state matches stateAfterIdats 0 (with expectedMetadata).
  have hOffsetEq : (33 + 8 + w.payload.size + 4 : Nat) = s.idatOffset 0 := by
    unfold idatOffset
    rw [s.preChunkWireSize_of_some hw]
    unfold MultiIdatContainerSpec.idatPrefixWireSize
    simp; omega
  have hStateEq :
      ({ header := some s.header, idat := ByteArray.empty,
         seenPLTE := false, seenIDAT := false, closedIDAT := false,
         metadata := w.expectedMetadata } : PngMetadataParseState) =
      s.stateAfterIdats 0 := by
    unfold stateAfterIdats expectedMetadata
    rw [hw]
    simp [List.foldl]
  rw [hOffsetEq, hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
lemma walk_ihdr_step {w : PreIdatChunk s.header} (hw : s.preChunk = some w) (fuel : Nat)
    (hFuel : s.idatChunks.length + 2 ≤ fuel)
    (hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by decide) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (8 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
  have hLen : (8 : Nat) + 3 < s.bytes.size := by omega
  have hReadIhdr := s.readChunk_g_ihdr hw hLen
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
  cases fuel with
  | zero => omega
  | succ fuel' =>
      have hFuel' : s.idatChunks.length + 1 ≤ fuel' := by omega
      have hWalk := s.walk_preChunk_step hw fuel' ?_
      · exact hWalk
      · cases fuel' with
        | zero => omega
        | succ fuel'' =>
            exact s.walk_idats_aux hw 0 (by omega) (fuel'' + 1) (by omega)

/-! ### Main theorems -/

/-- When no pre-chunk is present, the generic spec reduces to the
underlying multi-IDAT container; the parsePngForDecode correctness
follows from `parsePngForDecode_multiIdatContainerSpec_correct`. -/
lemma bytes_eq_multi_of_none (h : s.preChunk = none) :
    s.bytes = s.toMulti.bytes := by
  unfold bytes toMulti MultiIdatContainerSpec.bytes preChunkBytes
  rw [h]; simp

lemma expectedMetadata_of_none (h : s.preChunk = none) :
    s.expectedMetadata = PngMetadata.empty := by
  unfold expectedMetadata; rw [h]

theorem parsePngForDecode_correct_of_none (h : s.preChunk = none) :
    parsePngForDecode s.bytes
        (by rw [bytes_eq_multi_of_none s h]; exact s.toMulti.bytes_size_ge_8) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  rw [expectedMetadata_of_none s h]
  have hMulti := s.toMulti.parsePngForDecode_multiIdatContainerSpec_correct
  have hBytesEq : s.bytes = s.toMulti.bytes := bytes_eq_multi_of_none s h
  have hCongr :
      parsePngForDecode s.bytes
        (hBytesEq ▸ s.toMulti.bytes_size_ge_8) =
      parsePngForDecode s.toMulti.bytes s.toMulti.bytes_size_ge_8 := by
    congr 1
  rw [hCongr]
  show parsePngForDecode s.toMulti.bytes s.toMulti.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := PngMetadata.empty }
  exact hMulti

set_option maxHeartbeats 1600000 in
/-- The generic main theorem (for the `preChunk = some` case): walks the
parser through IHDR + pre-chunk + IDATs + IEND. -/
theorem parsePngForDecode_correct_of_some
    {w : PreIdatChunk s.header} (hw : s.preChunk = some w) :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  -- parsePngSimple returns none (third readChunk reads the pre-chunk's typeBytes
  -- which the simple parser expects to be idatTypeBytes; the witness's typeBytes
  -- is ≠ idatTypeBytes via its `hTypeNotIDAT` derivation from the layout).
  -- We don't have a direct hTypeNotIDAT field; rather, we know typeBytes is one of
  -- {tIME, pHYs, gAMA, cHRM, sRGB, tRNS, bKGD} via the instance construction.
  -- Here we instead just walk through parsePngWithMetadata directly.
  have hSimpleNone : parsePngSimple s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimple
    have hSig : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
    have hLen1 : (8 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
    have hLen2' : (33 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size, s.preChunkWireSize_of_some hw]; omega
    have hRead1 := s.readChunk_g_ihdr hw hLen1
    have hRead2 := s.readChunk_g_preChunk hw hLen2'
    have hCT256 : s.header.colorType < 256 := by
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
    have hBDlt : s.header.bitDepth < 256 := by
      rcases s.hBitDepth with h | h | h <;> rw [h] <;> decide
    have hParseHdr := parseIHDRData_encodeIHDRData_lt256 s.header
      s.hWidth s.hHeight hBDlt s.hInterlace hCT256
    have hCtBdOk :
        pngColorTypeBitDepthSupported s.header.colorType s.header.bitDepth = true :=
      s.hCtBdSupported
    have hCTProp :
        ¬s.header.colorType = 0 → ¬s.header.colorType = 2 →
          ¬s.header.colorType = 4 → s.header.colorType = 6 := by
      intro h0 h2 h4
      rcases s.hColorType with hc | hc | hc | hc
      · exact (h0 hc).elim
      · exact (h2 hc).elim
      · exact (h4 hc).elim
      · exact hc
    have hNotIDAT : (w.typeBytes != idatTypeBytes) = true := by
      have h := w.hTypeNotIDAT
      simp [bne, h]
    simp [hSig, hLen1, hRead1, hParseHdr, hCtBdOk,
          hLen2', hRead2, hNotIDAT,
          bne_self_eq_false' (a := ihdrTypeBytes)]
  have hSimpleMetaNone : parsePngSimpleWithMetadata s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimpleWithMetadata
    simp [hSimpleNone]
  have hSigExtract : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
  have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
    rw [hSigExtract]; exact bne_self_eq_false' (a := pngSignature)
  have hLoopFuel : s.idatChunks.length + 2 ≤ s.bytes.size := by
    rw [bytes_size, s.preChunkWireSize_of_some hw]
    unfold MultiIdatContainerSpec.idatTotalWireSize
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
  have hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by
    rw [encodeIHDRData_size s.header]; decide
  unfold parsePngForDecode parsePngWithMetadata
  simp [hSimpleMetaNone, hSigCheck]
  exact s.walk_ihdr_step hw s.bytes.size hLoopFuel hHeader

theorem parsePngForDecode_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  rcases h : s.preChunk with _ | w
  · -- preChunk = none: reduce via the multi-IDAT theorem
    have hNone := s.parsePngForDecode_correct_of_none h
    exact hNone
  · exact s.parsePngForDecode_correct_of_some h

end MultiIdatGenericPreChunkContainerSpec

end Lemmas

end Bitmaps
