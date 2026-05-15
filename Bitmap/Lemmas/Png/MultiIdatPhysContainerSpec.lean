import Bitmap.Lemmas.Png.MultiIdatContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `pHYs` (Step 2b)

`MultiIdatPhysContainerSpec` extends `MultiIdatContainerSpec` with an
optional `pHYs` chunk placed between IHDR and the first IDAT. This is
the simplest ancillary-chunk extension: `pHYs` carries a modification
physicalstamp that does not affect the decoder's color flow, so the
existing end-to-end pipeline applies almost verbatim.

The byte layout is

    signature ++ IHDR ++ (pHYs chunk, if any) ++ IDAT* ++ IEND.

The decoder pipeline records the parsed `PngPhysicalPixelDimensions` in the metadata's
`physical` field. Because `applyPngColorSpaceTransform` only
inspects the `srgb`/`chromaticities`/`gamma` fields, a `physical`-
only metadata behaves identically to `PngMetadata.empty` under the
color-space transform. -/

/-- A `pHYs` chunk witness: the raw 9-byte payload plus the decoded
`PngPhysicalPixelDimensions` and the round-trip witness `parsePhysData payload = some physical`. -/
structure PhysChunkWitness where
  payload : ByteArray
  physical : PngPhysicalPixelDimensions
  hParses : parsePhysData payload = some physical

/-- A PNG byte stream with the multi-IDAT shape plus an optional `pHYs`
chunk between IHDR and the first IDAT. -/
structure MultiIdatPhysContainerSpec where
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
  /-- Optional `pHYs` chunk placed between IHDR and the first IDAT. -/
  pHYs : Option PhysChunkWitness

namespace MultiIdatPhysContainerSpec

variable (s : MultiIdatPhysContainerSpec)

/-- The underlying multi-IDAT spec (forgetting the `pHYs` data). -/
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

/-- The wrapped `pHYs` chunk bytes (12-byte overhead + 9-byte payload), or
the empty byte array when no `pHYs` chunk is present. -/
def physChunkBytes : ByteArray :=
  match s.pHYs with
  | none => ByteArray.empty
  | some w => mkChunkBytes physTypeBytes w.payload

/-- Wire size of the `pHYs` chunk: 21 bytes when present, 0 otherwise. -/
def pHYsWireSize : Nat :=
  if s.pHYs.isSome then 21 else 0

/-- The byte layout: signature, IHDR, optional pHYs, concatenated IDATs, IEND. -/
def bytes : ByteArray :=
  pngSignature ++
  mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
  s.physChunkBytes ++
  s.toMulti.idatChunksBytes ++
  mkChunkBytes iendTypeBytes ByteArray.empty

/-- The concatenated IDAT payload — same as the underlying multi-IDAT. -/
def idatData : ByteArray :=
  s.toMulti.idatData

/-- The metadata produced by parsing the byte stream: empty plus the
`pHYs` physical, if any. -/
def expectedMetadata : PngMetadata :=
  match s.pHYs with
  | none => PngMetadata.empty
  | some w => { PngMetadata.empty with physical := some w.physical }

/-- Bytes layout reduces to the multi-IDAT layout when no `pHYs` is present. -/
lemma bytes_eq_multi_of_none (h : s.pHYs = none) :
    s.bytes = s.toMulti.bytes := by
  unfold bytes toMulti MultiIdatContainerSpec.bytes physChunkBytes
  rw [h]
  simp

/-- The expected metadata is empty when no `pHYs` is present. -/
lemma expectedMetadata_of_none (h : s.pHYs = none) :
    s.expectedMetadata = PngMetadata.empty := by
  unfold expectedMetadata; rw [h]

/-! ### Helpers for the `pHYs = some` case -/

/-- If `pHYs = some w`, the witness payload has the canonical 9-byte length. -/
lemma physWitness_payload_size {w : PhysChunkWitness} : w.payload.size = 9 := by
  -- parsePhysData first rejects size ≠ 7, so the round-trip witness fixes it.
  have h := w.hParses
  unfold parsePhysData at h
  by_contra hne
  simp [hne] at h

/-- The wrapped `pHYs` chunk bytes have size 21 when `pHYs = some w`. -/
lemma physChunkBytes_size_of_some {w : PhysChunkWitness} (h : s.pHYs = some w) :
    s.physChunkBytes.size = 21 := by
  unfold physChunkBytes
  rw [h]
  rw [mkChunkBytes_size physTypeBytes w.payload (by rfl : physTypeBytes.size = 4)]
  rw [physWitness_payload_size]

/-- `pHYsWireSize` equals 21 when `pHYs = some w`. -/
lemma pHYsWireSize_of_some {w : PhysChunkWitness} (h : s.pHYs = some w) :
    s.pHYsWireSize = 21 := by
  unfold pHYsWireSize
  rw [h]
  simp

/-- `pHYsWireSize` equals 0 when `pHYs = none`. -/
lemma pHYsWireSize_of_none (h : s.pHYs = none) :
    s.pHYsWireSize = 0 := by
  unfold pHYsWireSize
  rw [h]
  simp

/-! ### Bytes size and position arithmetic -/

/-- Total bytes size: 8 (sig) + 25 (IHDR) + pHYs (0 or 21) + IDATs + 12 (IEND). -/
lemma bytes_size :
    s.bytes.size =
      45 + s.pHYsWireSize + s.toMulti.idatTotalWireSize := by
  unfold bytes
  have hIhdrSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  have hIendSize :
      (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]; simp
  have hPhysSize : s.physChunkBytes.size = s.pHYsWireSize := by
    unfold pHYsWireSize
    match h : s.pHYs with
    | none => unfold physChunkBytes; rw [h]; simp
    | some w =>
        rw [s.physChunkBytes_size_of_some h]
        simp
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
      ByteArray.size_append, pngSignature_size, hIhdrSize, hPhysSize,
      hIdatSize, hIendSize]
  omega

/-- Every multi-IDAT-with-physical byte stream is at least 8 bytes long. -/
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := by
  rw [bytes_size]; omega

/-- Byte offset of the i-th IDAT chunk's first byte. -/
def idatOffsetP (i : Nat) : Nat :=
  33 + s.pHYsWireSize + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i

/-- Byte offset of the IEND chunk. -/
def iendOffsetP : Nat :=
  33 + s.pHYsWireSize + s.toMulti.idatTotalWireSize

/-! ### Bytes-extract lemmas (`pHYs = some` case)

These mirror the multi-IDAT `bytes_extract_*` helpers. We first
right-associate the concatenation so the signature is on the left
(`bytes_eq_signature_then_rest`), then peel off prefixes with
`byteArray_extract_append_prefix`. -/

/-- Right-associated form of the byte layout: `signature ++ (rest)`. -/
lemma bytes_eq_signature_then_rest :
    s.bytes =
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (s.physChunkBytes ++
            (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))) := by
  unfold bytes
  simp [ByteArray.append_assoc]

/-- Signature lives in the first 8 bytes. -/
lemma bytes_extract_signature : s.bytes.extract 0 8 = pngSignature := by
  rw [s.bytes_eq_signature_then_rest]
  have hSig : pngSignature.size = 8 := pngSignature_size
  rw [byteArray_extract_append_prefix
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (s.physChunkBytes ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)))
    (n := 8) (by simp [hSig])]
  rw [← hSig]
  exact ByteArray.extract_zero_size

/-- Slicing past the signature gives access to the rest. -/
lemma bytes_extract_skip_signature (start finish : Nat)
    (_h : 8 + finish ≤ s.bytes.size) :
    s.bytes.extract (8 + start) (8 + finish) =
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        (s.physChunkBytes ++
          (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))).extract
        start finish := by
  rw [s.bytes_eq_signature_then_rest]
  have hSig : pngSignature.size = 8 := pngSignature_size
  have h' := ByteArray.extract_append_size_add
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (s.physChunkBytes ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)))
    (i := start) (j := finish)
  simpa [hSig] using h'

/-- IHDR lives at byte 8 with size 25. -/
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
    (b := s.physChunkBytes ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (n := 25) (by rw [hIhdrChunkSize])]
  rw [show (25 : Nat) = (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size from
    hIhdrChunkSize.symm]
  exact ByteArray.extract_zero_size

/-- Slicing past signature + IHDR gives access to the (pHYs ++ IDATs ++ IEND) region. -/
lemma bytes_extract_skip_through_ihdr (start finish : Nat)
    (_h : 33 + finish ≤ s.bytes.size) :
    s.bytes.extract (33 + start) (33 + finish) =
      (s.physChunkBytes ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)).extract
        start finish := by
  have hSig : pngSignature.size = 8 := pngSignature_size
  have hIhdr : (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  have h1 : 8 + (25 + finish) ≤ s.bytes.size := by
    rw [bytes_size] at _h
    rw [bytes_size]
    omega
  have hSkip := s.bytes_extract_skip_signature (25 + start) (25 + finish) h1
  rw [show (8 : Nat) + (25 + start) = 33 + start from by omega] at hSkip
  rw [show (8 : Nat) + (25 + finish) = 33 + finish from by omega] at hSkip
  rw [hSkip]
  have hExt := ByteArray.extract_append_size_add
    (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
    (b := s.physChunkBytes ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (i := start) (j := finish)
  simpa [hIhdr] using hExt

/-- pHYs chunk lives at byte 33 with size 21 (when present). -/
lemma bytes_extract_pHYs {w : PhysChunkWitness} (hw : s.pHYs = some w) :
    s.bytes.extract 33 (33 + 12 + w.payload.size) =
      mkChunkBytes physTypeBytes w.payload := by
  rw [physWitness_payload_size (w := w)]
  have hPhysChunkSize : s.physChunkBytes.size = 21 :=
    s.physChunkBytes_size_of_some hw
  have hSizeBound : 33 + 21 ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw]; omega
  have hSkip := s.bytes_extract_skip_through_ihdr 0 21 hSizeBound
  rw [show (33 : Nat) + 0 = 33 from rfl] at hSkip
  rw [show (33 : Nat) + 21 = 33 + 12 + 9 from rfl] at hSkip
  rw [hSkip]
  rw [byteArray_extract_append_prefix
    (a := s.physChunkBytes)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (n := 21) (by rw [hPhysChunkSize])]
  rw [show (21 : Nat) = s.physChunkBytes.size from hPhysChunkSize.symm]
  rw [ByteArray.extract_zero_size]
  unfold physChunkBytes
  rw [hw]

/-- Slicing past signature + IHDR + pHYs (when present) reveals the
`(idatChunksBytes ++ IEND)` suffix — identical in shape to the multi-IDAT
case past IHDR. -/
lemma bytes_extract_skip_through_phys {w : PhysChunkWitness} (hw : s.pHYs = some w)
    (start finish : Nat) (_h : 54 + finish ≤ s.bytes.size) :
    s.bytes.extract (54 + start) (54 + finish) =
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty).extract
        start finish := by
  have hPhysChunkSize : s.physChunkBytes.size = 21 :=
    s.physChunkBytes_size_of_some hw
  have h1 : 33 + (21 + finish) ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw] at _h
    rw [bytes_size, s.pHYsWireSize_of_some hw]
    omega
  have hSkip := s.bytes_extract_skip_through_ihdr (21 + start) (21 + finish) h1
  rw [show (33 : Nat) + (21 + start) = 54 + start from by omega] at hSkip
  rw [show (33 : Nat) + (21 + finish) = 54 + finish from by omega] at hSkip
  rw [hSkip]
  have hExt := ByteArray.extract_append_size_add
    (a := s.physChunkBytes)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  simpa [hPhysChunkSize] using hExt

/-- The i-th wrapped IDAT chunk in `s.bytes` lives at the right offset. -/
lemma bytes_extract_idat_at_P {w : PhysChunkWitness} (hw : s.pHYs = some w) (i : Nat)
    (h : i < s.idatChunks.length) :
    s.bytes.extract (s.idatOffsetP i) (s.idatOffsetP (i + 1)) =
      mkChunkBytes idatTypeBytes s.idatChunks[i] := by
  unfold idatOffsetP
  rw [s.pHYsWireSize_of_some hw]
  -- 33 + 21 + prefix i = 54 + prefix i; same for i+1
  rw [show (33 : Nat) + 21 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i =
      54 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i from by omega]
  rw [show (33 : Nat) + 21 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) =
      54 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) from by omega]
  have hSizeBound :
      54 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw]
    show 54 + _ ≤ 45 + 21 + s.toMulti.idatTotalWireSize
    unfold MultiIdatContainerSpec.idatTotalWireSize
    show 54 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤
      45 + 21 + MultiIdatContainerSpec.idatPrefixWireSize s.toMulti.idatChunks
        s.toMulti.idatChunks.length
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    -- toMulti.idatChunks = s.idatChunks by rfl
    show 54 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤
      45 + 21 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length
    omega
  rw [s.bytes_extract_skip_through_phys hw
    (MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i)
    (MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1)) hSizeBound]
  -- Now the extract is within (idatChunksBytes ++ IEND).
  have hWithinIdat :
      MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤
        s.toMulti.idatChunksBytes.size := by
    rw [show s.toMulti.idatChunksBytes.size =
        MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length from ?_]
    · exact MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1) s.idatChunks.length (by omega)
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
  -- toMulti gives the same idatChunksBytes
  show (s.toMulti.idatChunksBytes).extract _ _ = _
  exact s.toMulti.idatChunksBytes_extract_at i h

/-- IEND lives at `iendOffsetP s` with size 12 (when pHYs = some). -/
lemma bytes_extract_iend_P {w : PhysChunkWitness} (hw : s.pHYs = some w) :
    s.bytes.extract s.iendOffsetP (s.iendOffsetP + 12) =
      mkChunkBytes iendTypeBytes ByteArray.empty := by
  unfold iendOffsetP
  rw [s.pHYsWireSize_of_some hw]
  -- 33 + 21 + idatTotalWireSize = 54 + idatTotalWireSize
  rw [show (33 : Nat) + 21 + s.toMulti.idatTotalWireSize =
      54 + s.toMulti.idatTotalWireSize from by omega]
  have hSizeBound : 54 + s.toMulti.idatTotalWireSize + 12 ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw]; omega
  have hSizeBound' : 54 + (s.toMulti.idatTotalWireSize + 12) ≤ s.bytes.size := by omega
  have hSkip := s.bytes_extract_skip_through_phys hw
    s.toMulti.idatTotalWireSize (s.toMulti.idatTotalWireSize + 12) hSizeBound'
  rw [show (54 : Nat) + s.toMulti.idatTotalWireSize + 12 =
      54 + (s.toMulti.idatTotalWireSize + 12) from by omega]
  rw [hSkip]
  -- (idatChunksBytes ++ IEND).extract idatTotalWireSize (idatTotalWireSize + 12) = IEND
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

/-! ### `readChunk` lemmas (`pHYs = some` case) -/

set_option maxHeartbeats 800000 in
/-- `readChunk` at byte 8 reads the IHDR chunk. -/
lemma readChunk_p_ihdr {w : PhysChunkWitness} (hw : s.pHYs = some w)
    (hLen : 8 + 3 < s.bytes.size) :
    readChunk s.bytes 8 hLen =
      some (ihdrTypeBytes, encodeIHDRData s.header, 33) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hSize : 8 + 12 + (encodeIHDRData s.header).size ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw, hIhdrSize]; omega
  have hIhdrFits : (encodeIHDRData s.header).size < 2 ^ 32 := by
    rw [hIhdrSize]; decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 8
    ihdrTypeBytes (encodeIHDRData s.header)
    (by rfl) hIhdrFits s.bytes_extract_ihdr hSize hLen
  rw [show 8 + 8 + (encodeIHDRData s.header).size + 4 = 33 from by rw [hIhdrSize]] at h
  exact h

set_option maxHeartbeats 800000 in
/-- `readChunk` at byte 33 reads the `pHYs` chunk (when present). -/
lemma readChunk_p_pHYs {w : PhysChunkWitness} (hw : s.pHYs = some w)
    (hLen : 33 + 3 < s.bytes.size) :
    readChunk s.bytes 33 hLen = some (physTypeBytes, w.payload, 54) := by
  have hPayloadSize : w.payload.size = 9 := physWitness_payload_size
  have hSize : 33 + 12 + w.payload.size ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw, hPayloadSize]; omega
  have hPayloadFits : w.payload.size < 2 ^ 32 := by rw [hPayloadSize]; decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 33
    physTypeBytes w.payload (by rfl) hPayloadFits (s.bytes_extract_pHYs hw) hSize hLen
  rw [show 33 + 8 + w.payload.size + 4 = 54 from by rw [hPayloadSize]] at h
  exact h

set_option maxHeartbeats 800000 in
/-- `readChunk` at `idatOffsetP s i` reads the i-th IDAT chunk. -/
lemma readChunk_p_idat {w : PhysChunkWitness} (hw : s.pHYs = some w) (i : Nat)
    (h : i < s.idatChunks.length)
    (hLen : s.idatOffsetP i + 3 < s.bytes.size) :
    readChunk s.bytes (s.idatOffsetP i) hLen =
      some (idatTypeBytes, s.idatChunks[i],
        s.idatOffsetP i + 8 + s.idatChunks[i].size + 4) := by
  have hChunkSize := s.hChunkSize s.idatChunks[i] (List.getElem_mem h)
  have hChunkRangeBound :
      s.idatOffsetP i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    unfold idatOffsetP
    rw [bytes_size, s.pHYsWireSize_of_some hw]
    have hStep := MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    -- toMulti.idatChunks = s.idatChunks
    show 33 + 21 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i + 12 +
      s.idatChunks[i].size ≤ 45 + 21 +
      MultiIdatContainerSpec.idatPrefixWireSize s.toMulti.idatChunks
        s.toMulti.idatChunks.length
    show _ ≤ 45 + 21 +
      MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length
    omega
  have hWrap :
      s.bytes.extract (s.idatOffsetP i) (s.idatOffsetP i + 12 + s.idatChunks[i].size) =
        mkChunkBytes idatTypeBytes s.idatChunks[i] := by
    have hWidth :
        s.idatOffsetP (i + 1) = s.idatOffsetP i + 12 + s.idatChunks[i].size := by
      unfold idatOffsetP
      rw [MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h]
      omega
    have hExt := s.bytes_extract_idat_at_P hw i h
    rw [← hWidth]; exact hExt
  exact MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes (s.idatOffsetP i)
    idatTypeBytes s.idatChunks[i] (by rfl) hChunkSize hWrap hChunkRangeBound hLen

set_option maxHeartbeats 800000 in
/-- `readChunk` at `iendOffsetP s` reads the IEND chunk. -/
lemma readChunk_p_iend {w : PhysChunkWitness} (hw : s.pHYs = some w)
    (hLen : s.iendOffsetP + 3 < s.bytes.size) :
    readChunk s.bytes s.iendOffsetP hLen =
      some (iendTypeBytes, ByteArray.empty, s.bytes.size) := by
  have hSize : s.iendOffsetP + 12 + ByteArray.empty.size ≤ s.bytes.size := by
    unfold iendOffsetP
    rw [bytes_size, s.pHYsWireSize_of_some hw]
    simp; omega
  have hEmptyFits : (ByteArray.empty : ByteArray).size < 2 ^ 32 := by decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes s.iendOffsetP
    iendTypeBytes ByteArray.empty (by rfl) hEmptyFits (s.bytes_extract_iend_P hw) hSize hLen
  rw [show s.iendOffsetP + 8 + ByteArray.empty.size + 4 = s.bytes.size from ?_] at h
  · exact h
  · unfold iendOffsetP
    rw [bytes_size, s.pHYsWireSize_of_some hw]
    simp; omega

/-! ### Walk lemmas (`pHYs = some` case)

The state-after-IDAT walk mirrors Phase 6b's `parsePngLoopFuelWithMetadata_walk_*`
chain. The only structural difference is the threaded metadata
(`expectedMetadata` carries the pHYs-derived `physical`). -/

/-- State after processing the first `i` IDAT chunks: header set, IDAT
accumulated, and metadata = `s.expectedMetadata` (the pHYs-derived
modification physical). -/
private def stateAfterIdatsMP (i : Nat) : PngMetadataParseState :=
  { header := some s.header
    idat := s.idatChunks.take i |>.foldl (· ++ ·) ByteArray.empty
    seenPLTE := false
    seenIDAT := 0 < i
    closedIDAT := false
    metadata := s.expectedMetadata }

/-- The accumulated `idat` after all `n` chunks equals `s.idatData`. -/
private lemma stateAfterIdatsMP_idat_full :
    (s.stateAfterIdatsMP s.idatChunks.length).idat = s.idatData := by
  unfold stateAfterIdatsMP idatData MultiIdatContainerSpec.idatData toMulti
  rw [List.take_length]

/-- The `idat` field accumulates one more chunk at each step. -/
private lemma stateAfterIdatsMP_idat_succ (i : Nat)
    (h : i < s.idatChunks.length) :
    (s.stateAfterIdatsMP (i + 1)).idat =
      (s.stateAfterIdatsMP i).idat ++ s.idatChunks[i] := by
  unfold stateAfterIdatsMP
  show (s.idatChunks.take (i + 1)).foldl (· ++ ·) ByteArray.empty =
    (s.idatChunks.take i).foldl (· ++ ·) ByteArray.empty ++ s.idatChunks[i]
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp [List.foldl]

set_option maxHeartbeats 1200000 in
/-- Walk one IDAT chunk in the metadata-aware loop with non-empty metadata. -/
lemma parsePngLoopFuelWithMetadata_walk_idat_step_P
    {w : PhysChunkWitness} (hw : s.pHYs = some w) (i : Nat)
    (h : i < s.idatChunks.length)
    (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffsetP (i + 1))
              (s.stateAfterIdatsMP (i + 1)) =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes (s.idatOffsetP i)
        (s.stateAfterIdatsMP i) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hChunkRangeBound :
      s.idatOffsetP i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    unfold idatOffsetP
    rw [bytes_size, s.pHYsWireSize_of_some hw]
    have hStep := MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  have hLen : s.idatOffsetP i + 3 < s.bytes.size := by omega
  have hPos : s.idatOffsetP i + 8 ≤ s.bytes.size := by omega
  have hReadIdat := s.readChunk_p_idat hw i h hLen
  have hNextOffsetEq :
      s.idatOffsetP i + 8 + s.idatChunks[i].size + 4 = s.idatOffsetP (i + 1) := by
    unfold idatOffsetP
    rw [MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h]
    omega
  rw [hNextOffsetEq] at hReadIdat
  have hStep := parsePngLoopFuelWithMetadata_idat_appends_when_open fuel s.bytes
    (s.idatOffsetP i) (s.stateAfterIdatsMP i) s.header idatTypeBytes
    s.idatChunks[i] (s.idatOffsetP (i + 1))
    hPos hLen hReadIdat
    (by unfold stateAfterIdatsMP; rfl)
    (by decide) (by decide) (by decide)
    (by unfold stateAfterIdatsMP; rfl)
    (by
      unfold stateAfterIdatsMP
      simp
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide)
  rw [hStep]
  have hIdatEq : (s.stateAfterIdatsMP i).idat ++ s.idatChunks[i] =
      (s.stateAfterIdatsMP (i + 1)).idat := by
    rw [s.stateAfterIdatsMP_idat_succ i h]
  have hStateEq :
      ({ header := some s.header
         idat := (s.stateAfterIdatsMP i).idat ++ s.idatChunks[i]
         seenPLTE := (s.stateAfterIdatsMP i).seenPLTE
         seenIDAT := true
         closedIDAT := false
         metadata := (s.stateAfterIdatsMP i).metadata : PngMetadataParseState }) =
      s.stateAfterIdatsMP (i + 1) := by
    rw [hIdatEq]
    unfold stateAfterIdatsMP
    rfl
  rw [hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
/-- Inductive walk over all remaining chunks plus IEND in the metadata case. -/
lemma parsePngLoopFuelWithMetadata_walk_idats_aux_P
    {w : PhysChunkWitness} (hw : s.pHYs = some w) (i : Nat)
    (hi : i ≤ s.idatChunks.length)
    (fuel : Nat) (hFuel : s.idatChunks.length - i + 1 ≤ fuel) :
    parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffsetP i)
      (s.stateAfterIdatsMP i) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  induction h : s.idatChunks.length - i generalizing i fuel with
  | zero =>
      have hin : i = s.idatChunks.length := by omega
      cases fuel with
      | zero =>
          rw [hin] at hFuel; simp at hFuel
      | succ fuel' =>
          have hOffsetEq : s.idatOffsetP i = s.iendOffsetP := by
            unfold idatOffsetP iendOffsetP MultiIdatContainerSpec.idatTotalWireSize
            rw [hin]
            rfl
          rw [hOffsetEq]
          have hLen : s.iendOffsetP + 3 < s.bytes.size := by
            unfold iendOffsetP
            rw [bytes_size, s.pHYsWireSize_of_some hw]
            omega
          have hPos : s.iendOffsetP + 8 ≤ s.bytes.size := by
            unfold iendOffsetP
            rw [bytes_size, s.pHYsWireSize_of_some hw]
            omega
          have hReadIend := s.readChunk_p_iend hw hLen
          have hSeenIDAT : (s.stateAfterIdatsMP i).seenIDAT = true := by
            unfold stateAfterIdatsMP
            simp
            rw [hin]
            cases hChunks : s.idatChunks with
            | nil => exact absurd hChunks s.hNonempty
            | cons _ _ => simp
          have hHeader : (s.stateAfterIdatsMP i).header = some s.header := rfl
          have hIdatEq : (s.stateAfterIdatsMP i).idat = s.idatData := by
            rw [hin]; exact s.stateAfterIdatsMP_idat_full
          have hMetaEq :
              (s.stateAfterIdatsMP i).metadata = s.expectedMetadata := rfl
          have hRes :=
            MultiIdatContainerSpec.parsePngLoopFuelWithMetadata_iend_success_step
              fuel' s.bytes s.iendOffsetP (s.stateAfterIdatsMP i) s.header
              hPos hLen hReadIend hHeader hSeenIDAT
          rw [hIdatEq, hMetaEq] at hRes
          exact hRes
  | succ k ih =>
      have hilt : i < s.idatChunks.length := by omega
      cases fuel with
      | zero =>
          have : s.idatChunks.length - i + 1 ≤ 0 := hFuel; omega
      | succ fuel' =>
          have hi' : i + 1 ≤ s.idatChunks.length := by omega
          have hk' : s.idatChunks.length - (i + 1) = k := by omega
          have hFuel' : s.idatChunks.length - (i + 1) + 1 ≤ fuel' := by
            have hkfuel : s.idatChunks.length - i + 1 ≤ fuel' + 1 := hFuel
            omega
          have hRest := ih (i := i + 1) hi' fuel' hFuel' hk'
          exact s.parsePngLoopFuelWithMetadata_walk_idat_step_P hw i hilt fuel' hRest

set_option maxHeartbeats 1200000 in
/-- Walk past the pHYs chunk: from pos 33 with the "just-after-IHDR" state,
read the pHYs chunk and recurse at pos 54 with metadata updated. -/
lemma parsePngLoopFuelWithMetadata_walk_pHYs_step
    {w : PhysChunkWitness} (hw : s.pHYs = some w)
    (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffsetP 0)
              (s.stateAfterIdatsMP 0) =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 33
        { header := some s.header, idat := ByteArray.empty,
          seenPLTE := false, seenIDAT := false, closedIDAT := false,
          metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (33 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw]; omega
  have hLen : (33 : Nat) + 3 < s.bytes.size := by omega
  have hReadPhys := s.readChunk_p_pHYs hw hLen
  -- Apply parsePngLoopFuelWithMetadata_accepts_pHYs.
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
  have hStep := parsePngLoopFuelWithMetadata_accepts_pHYs fuel s.bytes 33
    { header := some s.header, idat := ByteArray.empty,
      seenPLTE := false, seenIDAT := false, closedIDAT := false,
      metadata := PngMetadata.empty }
    s.header physTypeBytes w.payload 54 w.physical
    hPos hLen hReadPhys rfl
    hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS hNotBKGD
    hNotGAMA hNotCHRM hNotSRGB hNotTIME hIsPHYS rfl rfl w.hParses
  rw [hStep]
  -- Now the new state has metadata.physical := some w.physical.
  have hOffsetEq : (54 : Nat) = s.idatOffsetP 0 := by
    unfold idatOffsetP
    rw [s.pHYsWireSize_of_some hw]
    unfold MultiIdatContainerSpec.idatPrefixWireSize
    simp
  have hStateEq :
      ({ header := some s.header, idat := ByteArray.empty,
         seenPLTE := false, seenIDAT := false, closedIDAT := false,
         metadata := { (PngMetadata.empty : PngMetadata) with
           physical := some w.physical } } : PngMetadataParseState) =
      s.stateAfterIdatsMP 0 := by
    unfold stateAfterIdatsMP expectedMetadata
    rw [hw]
    simp [List.foldl]
  rw [hOffsetEq, hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
/-- Opening step (with-physical case): from the empty initial state at byte 8,
walk through IHDR, then pHYs, then all IDATs, then IEND. -/
lemma parsePngLoopFuelWithMetadata_walk_ihdr_step_P
    {w : PhysChunkWitness} (hw : s.pHYs = some w) (fuel : Nat)
    (hFuel : s.idatChunks.length + 2 ≤ fuel)
    (hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by decide) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (8 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw]; omega
  have hLen : (8 : Nat) + 3 < s.bytes.size := by omega
  have hReadIhdr := s.readChunk_p_ihdr hw hLen
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hCT256 : s.header.colorType < 256 := by
    rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
  have hParseHdr := parseIHDRData_encodeIHDRData s.header
    s.hWidth s.hHeight s.hBitDepth s.hInterlace hCT256
  conv => lhs; unfold parsePngLoopFuelWithMetadata
  -- Length-field check at byte 8.
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
  -- Now we need to walk from pos 33 with header set, through pHYs and IDATs.
  -- Need fuel ≥ 1 + length + 1 = length + 2.
  cases fuel with
  | zero => omega
  | succ fuel' =>
      have hFuel' : s.idatChunks.length + 1 ≤ fuel' := by omega
      have hWalk := s.parsePngLoopFuelWithMetadata_walk_pHYs_step hw fuel' ?_
      · exact hWalk
      · -- The aux walk needs fuel ≥ length - 0 + 1 = length + 1.
        cases fuel' with
        | zero => omega
        | succ fuel'' =>
            have hFuel'' : s.idatChunks.length + 1 ≤ fuel'' + 1 := by omega
            exact s.parsePngLoopFuelWithMetadata_walk_idats_aux_P hw 0
              (by omega) (fuel'' + 1) (by omega)

/-! ### Main theorem (`pHYs = some` case) -/

set_option maxHeartbeats 1600000 in
/-- The metadata-aware parser accepts the with-physical byte stream and
returns the expected header, IDAT, and metadata (with the
`physical` set from the `pHYs` witness). -/
theorem parsePngForDecode_multiIdatPhysContainerSpec_correct_of_some
    {w : PhysChunkWitness} (hw : s.pHYs = some w) :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  -- For length ≥ 1, parsePngSimple sees IHDR + pHYs chunk after IHDR — the
  -- third readChunk in parsePngSimple reads pHYs (not IDAT), so it returns
  -- none. Fall through to parsePngLoopFuelWithMetadata.
  have hSimpleNone : parsePngSimple s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimple
    -- Walk IHDR + pHYs (which appears at pos 33, but parsePngSimple expects IDAT).
    have hSig : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
    have hLen1 : (8 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size, s.pHYsWireSize_of_some hw]; omega
    have hLen2' : (33 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size, s.pHYsWireSize_of_some hw]; omega
    have hRead1 := s.readChunk_p_ihdr hw hLen1
    have hRead2 := s.readChunk_p_pHYs hw hLen2'
    -- typ2 = physTypeBytes ≠ idatTypeBytes ⇒ parsePngSimple returns none.
    have hPhysNeIdat : (physTypeBytes != idatTypeBytes) = true := by decide
    have hCT256 : s.header.colorType < 256 := by
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
    have hParseHdr := parseIHDRData_encodeIHDRData s.header
      s.hWidth s.hHeight s.hBitDepth s.hInterlace hCT256
    have hCtBdOk :
        pngColorTypeBitDepthSupported s.header.colorType s.header.bitDepth = true := by
      rw [s.hBitDepth]
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
    have hCTProp :
        ¬s.header.colorType = 0 → ¬s.header.colorType = 2 →
          ¬s.header.colorType = 4 → s.header.colorType = 6 := by
      intro h0 h2 h4
      rcases s.hColorType with hc | hc | hc | hc
      · exact (h0 hc).elim
      · exact (h2 hc).elim
      · exact (h4 hc).elim
      · exact hc
    simp [hSig, hLen1, hRead1, hParseHdr, hCtBdOk,
          hLen2', hRead2, hPhysNeIdat,
          bne_self_eq_false' (a := ihdrTypeBytes)]
  -- parsePngSimpleWithMetadata = none follows.
  have hSimpleMetaNone : parsePngSimpleWithMetadata s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimpleWithMetadata
    simp [hSimpleNone]
  -- Signature check passes.
  have hSigExtract : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
  have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
    rw [hSigExtract]; exact bne_self_eq_false' (a := pngSignature)
  -- Fuel sufficient for IHDR + pHYs + n IDATs + IEND.
  have hLoopFuel : s.idatChunks.length + 2 ≤ s.bytes.size := by
    rw [bytes_size, s.pHYsWireSize_of_some hw]
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
  exact s.parsePngLoopFuelWithMetadata_walk_ihdr_step_P hw s.bytes.size hLoopFuel hHeader

/-! ### Forward correctness — `pHYs = none` case via the multi-IDAT theorem -/

/-- When no `pHYs` chunk is present, the multi-IDAT-with-physical spec
reduces to a plain `MultiIdatContainerSpec`, and the
`parsePngForDecode` correctness theorem follows from
`parsePngForDecode_multiIdatContainerSpec_correct`. -/
theorem parsePngForDecode_multiIdatPhysContainerSpec_correct_of_none
    (h : s.pHYs = none) :
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

/-! ### Unified main theorem -/

/-- The unified main theorem: `parsePngForDecode` accepts any
`MultiIdatPhysContainerSpec` byte stream and returns the header,
concatenated IDAT data, and the expected metadata (with
`physical` set from the `pHYs` witness when present). -/
theorem parsePngForDecode_multiIdatPhysContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  rcases h : s.pHYs with _ | w
  · -- pHYs = none
    have hNone := s.parsePngForDecode_multiIdatPhysContainerSpec_correct_of_none h
    -- Byte-size proofs differ; parsePngForDecode is proof-irrelevant in its
    -- size hypothesis.
    exact hNone
  · -- pHYs = some w
    exact s.parsePngForDecode_multiIdatPhysContainerSpec_correct_of_some h

end MultiIdatPhysContainerSpec

end Lemmas

end Bitmaps
