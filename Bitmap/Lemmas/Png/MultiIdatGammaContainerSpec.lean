import Bitmap.Lemmas.Png.MultiIdatContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Multi-IDAT container spec with optional `gAMA` (Step 2c)

`MultiIdatGammaContainerSpec` extends `MultiIdatContainerSpec` with an
optional `gAMA` chunk placed between IHDR and the first IDAT. This is
the simplest ancillary-chunk extension: `gAMA` carries a modification
gammastamp that does not affect the decoder's color flow, so the
existing end-to-end pipeline applies almost verbatim.

The byte layout is

    signature ++ IHDR ++ (gAMA chunk, if any) ++ IDAT* ++ IEND.

The decoder pipeline records the parsed `Nat` in the metadata's
`gamma` field. Because `applyPngColorSpaceTransform` only
inspects the `srgb`/`chromaticities`/`gamma` fields, a `gamma`-
only metadata behaves identically to `PngMetadata.empty` under the
color-space transform. -/

/-- A `gAMA` chunk witness: the raw 4-byte payload plus the decoded
`Nat` and the round-trip witness `parseGammaData payload = some gamma`. -/
structure GammaChunkWitness where
  payload : ByteArray
  gamma : Nat
  hParses : parseGammaData payload = some gamma

/-- A PNG byte stream with the multi-IDAT shape plus an optional `gAMA`
chunk between IHDR and the first IDAT. -/
structure MultiIdatGammaContainerSpec where
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
  /-- Optional `gAMA` chunk placed between IHDR and the first IDAT. -/
  gAMA : Option GammaChunkWitness

namespace MultiIdatGammaContainerSpec

variable (s : MultiIdatGammaContainerSpec)

/-- The underlying multi-IDAT spec (forgetting the `gAMA` data). -/
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

/-- The wrapped `gAMA` chunk bytes (12-byte overhead + 4-byte payload), or
the empty byte array when no `gAMA` chunk is present. -/
def gamaChunkBytes : ByteArray :=
  match s.gAMA with
  | none => ByteArray.empty
  | some w => mkChunkBytes gamaTypeBytes w.payload

/-- Wire size of the `gAMA` chunk: 16 bytes when present, 0 otherwise. -/
def gAMAWireSize : Nat :=
  if s.gAMA.isSome then 16 else 0

/-- The byte layout: signature, IHDR, optional gAMA, concatenated IDATs, IEND. -/
def bytes : ByteArray :=
  pngSignature ++
  mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
  s.gamaChunkBytes ++
  s.toMulti.idatChunksBytes ++
  mkChunkBytes iendTypeBytes ByteArray.empty

/-- The concatenated IDAT payload — same as the underlying multi-IDAT. -/
def idatData : ByteArray :=
  s.toMulti.idatData

/-- The metadata produced by parsing the byte stream: empty plus the
`gAMA` gamma, if any. -/
def expectedMetadata : PngMetadata :=
  match s.gAMA with
  | none => PngMetadata.empty
  | some w => { PngMetadata.empty with gamma := some w.gamma }

/-- Bytes layout reduces to the multi-IDAT layout when no `gAMA` is present. -/
lemma bytes_eq_multi_of_none (h : s.gAMA = none) :
    s.bytes = s.toMulti.bytes := by
  unfold bytes toMulti MultiIdatContainerSpec.bytes gamaChunkBytes
  rw [h]
  simp

/-- The expected metadata is empty when no `gAMA` is present. -/
lemma expectedMetadata_of_none (h : s.gAMA = none) :
    s.expectedMetadata = PngMetadata.empty := by
  unfold expectedMetadata; rw [h]

/-! ### Helpers for the `gAMA = some` case -/

/-- If `gAMA = some w`, the witness payload has the canonical 4-byte length. -/
lemma gammaWitness_payload_size {w : GammaChunkWitness} : w.payload.size = 4 := by
  -- parseGammaData first rejects size ≠ 7, so the round-trip witness fixes it.
  have h := w.hParses
  unfold parseGammaData at h
  by_contra hne
  simp [hne] at h

/-- The wrapped `gAMA` chunk bytes have size 16 when `gAMA = some w`. -/
lemma gamaChunkBytes_size_of_some {w : GammaChunkWitness} (h : s.gAMA = some w) :
    s.gamaChunkBytes.size = 16 := by
  unfold gamaChunkBytes
  rw [h]
  rw [mkChunkBytes_size gamaTypeBytes w.payload (by rfl : gamaTypeBytes.size = 4)]
  rw [gammaWitness_payload_size]

/-- `gAMAWireSize` equals 16 when `gAMA = some w`. -/
lemma gAMAWireSize_of_some {w : GammaChunkWitness} (h : s.gAMA = some w) :
    s.gAMAWireSize = 16 := by
  unfold gAMAWireSize
  rw [h]
  simp

/-- `gAMAWireSize` equals 0 when `gAMA = none`. -/
lemma gAMAWireSize_of_none (h : s.gAMA = none) :
    s.gAMAWireSize = 0 := by
  unfold gAMAWireSize
  rw [h]
  simp

/-! ### Bytes size and position arithmetic -/

/-- Total bytes size: 8 (sig) + 25 (IHDR) + gAMA (0 or 16) + IDATs + 12 (IEND). -/
lemma bytes_size :
    s.bytes.size =
      45 + s.gAMAWireSize + s.toMulti.idatTotalWireSize := by
  unfold bytes
  have hIhdrSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  have hIendSize :
      (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]; simp
  have hGammaSize : s.gamaChunkBytes.size = s.gAMAWireSize := by
    unfold gAMAWireSize
    match h : s.gAMA with
    | none => unfold gamaChunkBytes; rw [h]; simp
    | some w =>
        rw [s.gamaChunkBytes_size_of_some h]
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
      ByteArray.size_append, pngSignature_size, hIhdrSize, hGammaSize,
      hIdatSize, hIendSize]
  omega

/-- Every multi-IDAT-with-gamma byte stream is at least 8 bytes long. -/
lemma bytes_size_ge_8 : 8 ≤ s.bytes.size := by
  rw [bytes_size]; omega

/-- Byte offset of the i-th IDAT chunk's first byte. -/
def idatOffsetG (i : Nat) : Nat :=
  33 + s.gAMAWireSize + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i

/-- Byte offset of the IEND chunk. -/
def iendOffsetG : Nat :=
  33 + s.gAMAWireSize + s.toMulti.idatTotalWireSize

/-! ### Bytes-extract lemmas (`gAMA = some` case)

These mirror the multi-IDAT `bytes_extract_*` helpers. We first
right-associate the concatenation so the signature is on the left
(`bytes_eq_signature_then_rest`), then peel off prefixes with
`byteArray_extract_append_prefix`. -/

/-- Right-associated form of the byte layout: `signature ++ (rest)`. -/
lemma bytes_eq_signature_then_rest :
    s.bytes =
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (s.gamaChunkBytes ++
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
      (s.gamaChunkBytes ++
        (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)))
    (n := 8) (by simp [hSig])]
  rw [← hSig]
  exact ByteArray.extract_zero_size

/-- Slicing past the signature gives access to the rest. -/
lemma bytes_extract_skip_signature (start finish : Nat)
    (_h : 8 + finish ≤ s.bytes.size) :
    s.bytes.extract (8 + start) (8 + finish) =
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        (s.gamaChunkBytes ++
          (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))).extract
        start finish := by
  rw [s.bytes_eq_signature_then_rest]
  have hSig : pngSignature.size = 8 := pngSignature_size
  have h' := ByteArray.extract_append_size_add
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (s.gamaChunkBytes ++
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
    (b := s.gamaChunkBytes ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (n := 25) (by rw [hIhdrChunkSize])]
  rw [show (25 : Nat) = (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size from
    hIhdrChunkSize.symm]
  exact ByteArray.extract_zero_size

/-- Slicing past signature + IHDR gives access to the (gAMA ++ IDATs ++ IEND) region. -/
lemma bytes_extract_skip_through_ihdr (start finish : Nat)
    (_h : 33 + finish ≤ s.bytes.size) :
    s.bytes.extract (33 + start) (33 + finish) =
      (s.gamaChunkBytes ++
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
    (b := s.gamaChunkBytes ++
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (i := start) (j := finish)
  simpa [hIhdr] using hExt

/-- gAMA chunk lives at byte 33 with size 16 (when present). -/
lemma bytes_extract_gAMA {w : GammaChunkWitness} (hw : s.gAMA = some w) :
    s.bytes.extract 33 (33 + 12 + w.payload.size) =
      mkChunkBytes gamaTypeBytes w.payload := by
  rw [gammaWitness_payload_size (w := w)]
  have hGammaChunkSize : s.gamaChunkBytes.size = 16 :=
    s.gamaChunkBytes_size_of_some hw
  have hSizeBound : 33 + 16 ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw]; omega
  have hSkip := s.bytes_extract_skip_through_ihdr 0 16 hSizeBound
  rw [show (33 : Nat) + 0 = 33 from rfl] at hSkip
  rw [show (33 : Nat) + 16 = 33 + 12 + 4 from rfl] at hSkip
  rw [hSkip]
  rw [byteArray_extract_append_prefix
    (a := s.gamaChunkBytes)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (n := 16) (by rw [hGammaChunkSize])]
  rw [show (16 : Nat) = s.gamaChunkBytes.size from hGammaChunkSize.symm]
  rw [ByteArray.extract_zero_size]
  unfold gamaChunkBytes
  rw [hw]

/-- Slicing past signature + IHDR + gAMA (when present) reveals the
`(idatChunksBytes ++ IEND)` suffix — identical in shape to the multi-IDAT
case past IHDR. -/
lemma bytes_extract_skip_through_gamma {w : GammaChunkWitness} (hw : s.gAMA = some w)
    (start finish : Nat) (_h : 49 + finish ≤ s.bytes.size) :
    s.bytes.extract (49 + start) (49 + finish) =
      (s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty).extract
        start finish := by
  have hGammaChunkSize : s.gamaChunkBytes.size = 16 :=
    s.gamaChunkBytes_size_of_some hw
  have h1 : 33 + (16 + finish) ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw] at _h
    rw [bytes_size, s.gAMAWireSize_of_some hw]
    omega
  have hSkip := s.bytes_extract_skip_through_ihdr (16 + start) (16 + finish) h1
  rw [show (33 : Nat) + (16 + start) = 49 + start from by omega] at hSkip
  rw [show (33 : Nat) + (16 + finish) = 49 + finish from by omega] at hSkip
  rw [hSkip]
  have hExt := ByteArray.extract_append_size_add
    (a := s.gamaChunkBytes)
    (b := s.toMulti.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  simpa [hGammaChunkSize] using hExt

/-- The i-th wrapped IDAT chunk in `s.bytes` lives at the right offset. -/
lemma bytes_extract_idat_at_P {w : GammaChunkWitness} (hw : s.gAMA = some w) (i : Nat)
    (h : i < s.idatChunks.length) :
    s.bytes.extract (s.idatOffsetG i) (s.idatOffsetG (i + 1)) =
      mkChunkBytes idatTypeBytes s.idatChunks[i] := by
  unfold idatOffsetG
  rw [s.gAMAWireSize_of_some hw]
  -- 33 + 16 + prefix i = 49 + prefix i; same for i+1
  rw [show (33 : Nat) + 16 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i =
      49 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i from by omega]
  rw [show (33 : Nat) + 16 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) =
      49 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) from by omega]
  have hSizeBound :
      49 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw]
    show 49 + _ ≤ 45 + 16 + s.toMulti.idatTotalWireSize
    unfold MultiIdatContainerSpec.idatTotalWireSize
    show 49 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤
      45 + 16 + MultiIdatContainerSpec.idatPrefixWireSize s.toMulti.idatChunks
        s.toMulti.idatChunks.length
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    -- toMulti.idatChunks = s.idatChunks by rfl
    show 49 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks (i + 1) ≤
      45 + 16 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length
    omega
  rw [s.bytes_extract_skip_through_gamma hw
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

/-- IEND lives at `iendOffsetG s` with size 12 (when gAMA = some). -/
lemma bytes_extract_iend_P {w : GammaChunkWitness} (hw : s.gAMA = some w) :
    s.bytes.extract s.iendOffsetG (s.iendOffsetG + 12) =
      mkChunkBytes iendTypeBytes ByteArray.empty := by
  unfold iendOffsetG
  rw [s.gAMAWireSize_of_some hw]
  -- 33 + 16 + idatTotalWireSize = 49 + idatTotalWireSize
  rw [show (33 : Nat) + 16 + s.toMulti.idatTotalWireSize =
      49 + s.toMulti.idatTotalWireSize from by omega]
  have hSizeBound : 49 + s.toMulti.idatTotalWireSize + 12 ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw]; omega
  have hSizeBound' : 49 + (s.toMulti.idatTotalWireSize + 12) ≤ s.bytes.size := by omega
  have hSkip := s.bytes_extract_skip_through_gamma hw
    s.toMulti.idatTotalWireSize (s.toMulti.idatTotalWireSize + 12) hSizeBound'
  rw [show (49 : Nat) + s.toMulti.idatTotalWireSize + 12 =
      49 + (s.toMulti.idatTotalWireSize + 12) from by omega]
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

/-! ### `readChunk` lemmas (`gAMA = some` case) -/

set_option maxHeartbeats 800000 in
/-- `readChunk` at byte 8 reads the IHDR chunk. -/
lemma readChunk_p_ihdr {w : GammaChunkWitness} (hw : s.gAMA = some w)
    (hLen : 8 + 3 < s.bytes.size) :
    readChunk s.bytes 8 hLen =
      some (ihdrTypeBytes, encodeIHDRData s.header, 33) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hSize : 8 + 12 + (encodeIHDRData s.header).size ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw, hIhdrSize]; omega
  have hIhdrFits : (encodeIHDRData s.header).size < 2 ^ 32 := by
    rw [hIhdrSize]; decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 8
    ihdrTypeBytes (encodeIHDRData s.header)
    (by rfl) hIhdrFits s.bytes_extract_ihdr hSize hLen
  rw [show 8 + 8 + (encodeIHDRData s.header).size + 4 = 33 from by rw [hIhdrSize]] at h
  exact h

set_option maxHeartbeats 800000 in
/-- `readChunk` at byte 33 reads the `gAMA` chunk (when present). -/
lemma readChunk_p_gAMA {w : GammaChunkWitness} (hw : s.gAMA = some w)
    (hLen : 33 + 3 < s.bytes.size) :
    readChunk s.bytes 33 hLen = some (gamaTypeBytes, w.payload, 49) := by
  have hPayloadSize : w.payload.size = 4 := gammaWitness_payload_size
  have hSize : 33 + 12 + w.payload.size ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw, hPayloadSize]; omega
  have hPayloadFits : w.payload.size < 2 ^ 32 := by rw [hPayloadSize]; decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes 33
    gamaTypeBytes w.payload (by rfl) hPayloadFits (s.bytes_extract_gAMA hw) hSize hLen
  rw [show 33 + 8 + w.payload.size + 4 = 49 from by rw [hPayloadSize]] at h
  exact h

set_option maxHeartbeats 800000 in
/-- `readChunk` at `idatOffsetG s i` reads the i-th IDAT chunk. -/
lemma readChunk_p_idat {w : GammaChunkWitness} (hw : s.gAMA = some w) (i : Nat)
    (h : i < s.idatChunks.length)
    (hLen : s.idatOffsetG i + 3 < s.bytes.size) :
    readChunk s.bytes (s.idatOffsetG i) hLen =
      some (idatTypeBytes, s.idatChunks[i],
        s.idatOffsetG i + 8 + s.idatChunks[i].size + 4) := by
  have hChunkSize := s.hChunkSize s.idatChunks[i] (List.getElem_mem h)
  have hChunkRangeBound :
      s.idatOffsetG i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    unfold idatOffsetG
    rw [bytes_size, s.gAMAWireSize_of_some hw]
    have hStep := MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    -- toMulti.idatChunks = s.idatChunks
    show 33 + 16 + MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks i + 12 +
      s.idatChunks[i].size ≤ 45 + 16 +
      MultiIdatContainerSpec.idatPrefixWireSize s.toMulti.idatChunks
        s.toMulti.idatChunks.length
    show _ ≤ 45 + 16 +
      MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length
    omega
  have hWrap :
      s.bytes.extract (s.idatOffsetG i) (s.idatOffsetG i + 12 + s.idatChunks[i].size) =
        mkChunkBytes idatTypeBytes s.idatChunks[i] := by
    have hWidth :
        s.idatOffsetG (i + 1) = s.idatOffsetG i + 12 + s.idatChunks[i].size := by
      unfold idatOffsetG
      rw [MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h]
      omega
    have hExt := s.bytes_extract_idat_at_P hw i h
    rw [← hWidth]; exact hExt
  exact MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes (s.idatOffsetG i)
    idatTypeBytes s.idatChunks[i] (by rfl) hChunkSize hWrap hChunkRangeBound hLen

set_option maxHeartbeats 800000 in
/-- `readChunk` at `iendOffsetG s` reads the IEND chunk. -/
lemma readChunk_p_iend {w : GammaChunkWitness} (hw : s.gAMA = some w)
    (hLen : s.iendOffsetG + 3 < s.bytes.size) :
    readChunk s.bytes s.iendOffsetG hLen =
      some (iendTypeBytes, ByteArray.empty, s.bytes.size) := by
  have hSize : s.iendOffsetG + 12 + ByteArray.empty.size ≤ s.bytes.size := by
    unfold iendOffsetG
    rw [bytes_size, s.gAMAWireSize_of_some hw]
    simp; omega
  have hEmptyFits : (ByteArray.empty : ByteArray).size < 2 ^ 32 := by decide
  have h := MultiIdatContainerSpec.readChunk_at_mkChunkBytes s.bytes s.iendOffsetG
    iendTypeBytes ByteArray.empty (by rfl) hEmptyFits (s.bytes_extract_iend_P hw) hSize hLen
  rw [show s.iendOffsetG + 8 + ByteArray.empty.size + 4 = s.bytes.size from ?_] at h
  · exact h
  · unfold iendOffsetG
    rw [bytes_size, s.gAMAWireSize_of_some hw]
    simp; omega

/-! ### Walk lemmas (`gAMA = some` case)

The state-after-IDAT walk mirrors Phase 6b's `parsePngLoopFuelWithMetadata_walk_*`
chain. The only structural difference is the threaded metadata
(`expectedMetadata` carries the gAMA-derived `gamma`). -/

/-- State after processing the first `i` IDAT chunks: header set, IDAT
accumulated, and metadata = `s.expectedMetadata` (the gAMA-derived
modification gamma). -/
private def stateAfterIdatsMG (i : Nat) : PngMetadataParseState :=
  { header := some s.header
    idat := s.idatChunks.take i |>.foldl (· ++ ·) ByteArray.empty
    seenPLTE := false
    seenIDAT := 0 < i
    closedIDAT := false
    metadata := s.expectedMetadata }

/-- The accumulated `idat` after all `n` chunks equals `s.idatData`. -/
private lemma stateAfterIdatsMG_idat_full :
    (s.stateAfterIdatsMG s.idatChunks.length).idat = s.idatData := by
  unfold stateAfterIdatsMG idatData MultiIdatContainerSpec.idatData toMulti
  rw [List.take_length]

/-- The `idat` field accumulates one more chunk at each step. -/
private lemma stateAfterIdatsMG_idat_succ (i : Nat)
    (h : i < s.idatChunks.length) :
    (s.stateAfterIdatsMG (i + 1)).idat =
      (s.stateAfterIdatsMG i).idat ++ s.idatChunks[i] := by
  unfold stateAfterIdatsMG
  show (s.idatChunks.take (i + 1)).foldl (· ++ ·) ByteArray.empty =
    (s.idatChunks.take i).foldl (· ++ ·) ByteArray.empty ++ s.idatChunks[i]
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp [List.foldl]

set_option maxHeartbeats 1200000 in
/-- Walk one IDAT chunk in the metadata-aware loop with non-empty metadata. -/
lemma parsePngLoopFuelWithMetadata_walk_idat_step_P
    {w : GammaChunkWitness} (hw : s.gAMA = some w) (i : Nat)
    (h : i < s.idatChunks.length)
    (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffsetG (i + 1))
              (s.stateAfterIdatsMG (i + 1)) =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes (s.idatOffsetG i)
        (s.stateAfterIdatsMG i) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hChunkRangeBound :
      s.idatOffsetG i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    unfold idatOffsetG
    rw [bytes_size, s.gAMAWireSize_of_some hw]
    have hStep := MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h
    have hmono := MultiIdatContainerSpec.idatPrefixWireSize_mono s.idatChunks (i + 1)
      s.idatChunks.length (by omega)
    unfold MultiIdatContainerSpec.idatTotalWireSize
    have hChunkEq : s.toMulti.idatChunks = s.idatChunks := rfl
    rw [hChunkEq]
    omega
  have hLen : s.idatOffsetG i + 3 < s.bytes.size := by omega
  have hPos : s.idatOffsetG i + 8 ≤ s.bytes.size := by omega
  have hReadIdat := s.readChunk_p_idat hw i h hLen
  have hNextOffsetEq :
      s.idatOffsetG i + 8 + s.idatChunks[i].size + 4 = s.idatOffsetG (i + 1) := by
    unfold idatOffsetG
    rw [MultiIdatContainerSpec.idatPrefixWireSize_succ s.idatChunks i h]
    omega
  rw [hNextOffsetEq] at hReadIdat
  have hStep := parsePngLoopFuelWithMetadata_idat_appends_when_open fuel s.bytes
    (s.idatOffsetG i) (s.stateAfterIdatsMG i) s.header idatTypeBytes
    s.idatChunks[i] (s.idatOffsetG (i + 1))
    hPos hLen hReadIdat
    (by unfold stateAfterIdatsMG; rfl)
    (by decide) (by decide) (by decide)
    (by unfold stateAfterIdatsMG; rfl)
    (by
      unfold stateAfterIdatsMG
      simp
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide)
  rw [hStep]
  have hIdatEq : (s.stateAfterIdatsMG i).idat ++ s.idatChunks[i] =
      (s.stateAfterIdatsMG (i + 1)).idat := by
    rw [s.stateAfterIdatsMG_idat_succ i h]
  have hStateEq :
      ({ header := some s.header
         idat := (s.stateAfterIdatsMG i).idat ++ s.idatChunks[i]
         seenPLTE := (s.stateAfterIdatsMG i).seenPLTE
         seenIDAT := true
         closedIDAT := false
         metadata := (s.stateAfterIdatsMG i).metadata : PngMetadataParseState }) =
      s.stateAfterIdatsMG (i + 1) := by
    rw [hIdatEq]
    unfold stateAfterIdatsMG
    rfl
  rw [hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
/-- Inductive walk over all remaining chunks plus IEND in the metadata case. -/
lemma parsePngLoopFuelWithMetadata_walk_idats_aux_P
    {w : GammaChunkWitness} (hw : s.gAMA = some w) (i : Nat)
    (hi : i ≤ s.idatChunks.length)
    (fuel : Nat) (hFuel : s.idatChunks.length - i + 1 ≤ fuel) :
    parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffsetG i)
      (s.stateAfterIdatsMG i) =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  induction h : s.idatChunks.length - i generalizing i fuel with
  | zero =>
      have hin : i = s.idatChunks.length := by omega
      cases fuel with
      | zero =>
          rw [hin] at hFuel; simp at hFuel
      | succ fuel' =>
          have hOffsetEq : s.idatOffsetG i = s.iendOffsetG := by
            unfold idatOffsetG iendOffsetG MultiIdatContainerSpec.idatTotalWireSize
            rw [hin]
            rfl
          rw [hOffsetEq]
          have hLen : s.iendOffsetG + 3 < s.bytes.size := by
            unfold iendOffsetG
            rw [bytes_size, s.gAMAWireSize_of_some hw]
            omega
          have hPos : s.iendOffsetG + 8 ≤ s.bytes.size := by
            unfold iendOffsetG
            rw [bytes_size, s.gAMAWireSize_of_some hw]
            omega
          have hReadIend := s.readChunk_p_iend hw hLen
          have hSeenIDAT : (s.stateAfterIdatsMG i).seenIDAT = true := by
            unfold stateAfterIdatsMG
            simp
            rw [hin]
            cases hChunks : s.idatChunks with
            | nil => exact absurd hChunks s.hNonempty
            | cons _ _ => simp
          have hHeader : (s.stateAfterIdatsMG i).header = some s.header := rfl
          have hIdatEq : (s.stateAfterIdatsMG i).idat = s.idatData := by
            rw [hin]; exact s.stateAfterIdatsMG_idat_full
          have hMetaEq :
              (s.stateAfterIdatsMG i).metadata = s.expectedMetadata := rfl
          have hRes :=
            MultiIdatContainerSpec.parsePngLoopFuelWithMetadata_iend_success_step
              fuel' s.bytes s.iendOffsetG (s.stateAfterIdatsMG i) s.header
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
/-- Walk past the gAMA chunk: from pos 33 with the "just-after-IHDR" state,
read the gAMA chunk and recurse at pos 49 with metadata updated. -/
lemma parsePngLoopFuelWithMetadata_walk_gAMA_step
    {w : GammaChunkWitness} (hw : s.gAMA = some w)
    (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (s.idatOffsetG 0)
              (s.stateAfterIdatsMG 0) =
              some { header := s.header, idat := s.idatData,
                     metadata := s.expectedMetadata }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 33
        { header := some s.header, idat := ByteArray.empty,
          seenPLTE := false, seenIDAT := false, closedIDAT := false,
          metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (33 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw]; omega
  have hLen : (33 : Nat) + 3 < s.bytes.size := by omega
  have hReadGamma := s.readChunk_p_gAMA hw hLen
  -- Apply parsePngLoopFuelWithMetadata_accepts_gAMA.
  have hNotIHDR : (gamaTypeBytes == ihdrTypeBytes) = false := by decide
  have hNotPLTE : (gamaTypeBytes == plteTypeBytes) = false := by decide
  have hNotIDAT : (gamaTypeBytes == idatTypeBytes) = false := by decide
  have hNotIEND : (gamaTypeBytes == iendTypeBytes) = false := by decide
  have hNotTRNS : (gamaTypeBytes == trnsTypeBytes) = false := by decide
  have hNotBKGD : (gamaTypeBytes == bkgdTypeBytes) = false := by decide
  have hIsGAMA : (gamaTypeBytes == gamaTypeBytes) = true := by decide
  have hStep := parsePngLoopFuelWithMetadata_accepts_gAMA fuel s.bytes 33
    { header := some s.header, idat := ByteArray.empty,
      seenPLTE := false, seenIDAT := false, closedIDAT := false,
      metadata := PngMetadata.empty }
    s.header gamaTypeBytes w.payload 49 w.gamma
    hPos hLen hReadGamma rfl
    hNotIHDR hNotPLTE hNotIDAT hNotIEND hNotTRNS hNotBKGD
    hIsGAMA
    (show ((false : Bool) || (false : Bool)) = false from rfl)
    (show (PngMetadata.empty.gamma.isSome : Bool) = false from rfl)
    rfl
    w.hParses
  rw [hStep]
  -- Now the new state has metadata.gamma := some w.gamma.
  have hOffsetEq : (49 : Nat) = s.idatOffsetG 0 := by
    unfold idatOffsetG
    rw [s.gAMAWireSize_of_some hw]
    unfold MultiIdatContainerSpec.idatPrefixWireSize
    simp
  have hStateEq :
      ({ header := some s.header, idat := ByteArray.empty,
         seenPLTE := false, seenIDAT := false, closedIDAT := false,
         metadata := { (PngMetadata.empty : PngMetadata) with
           gamma := some w.gamma } } : PngMetadataParseState) =
      s.stateAfterIdatsMG 0 := by
    unfold stateAfterIdatsMG expectedMetadata
    rw [hw]
    simp [List.foldl]
  rw [hOffsetEq, hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
/-- Opening step (with-gamma case): from the empty initial state at byte 8,
walk through IHDR, then gAMA, then all IDATs, then IEND. -/
lemma parsePngLoopFuelWithMetadata_walk_ihdr_step_P
    {w : GammaChunkWitness} (hw : s.gAMA = some w) (fuel : Nat)
    (hFuel : s.idatChunks.length + 2 ≤ fuel)
    (hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by decide) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  have hPos : (8 : Nat) + 8 ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw]; omega
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
  -- Now we need to walk from pos 33 with header set, through gAMA and IDATs.
  -- Need fuel ≥ 1 + length + 1 = length + 2.
  cases fuel with
  | zero => omega
  | succ fuel' =>
      have hFuel' : s.idatChunks.length + 1 ≤ fuel' := by omega
      have hWalk := s.parsePngLoopFuelWithMetadata_walk_gAMA_step hw fuel' ?_
      · exact hWalk
      · -- The aux walk needs fuel ≥ length - 0 + 1 = length + 1.
        cases fuel' with
        | zero => omega
        | succ fuel'' =>
            have hFuel'' : s.idatChunks.length + 1 ≤ fuel'' + 1 := by omega
            exact s.parsePngLoopFuelWithMetadata_walk_idats_aux_P hw 0
              (by omega) (fuel'' + 1) (by omega)

/-! ### Main theorem (`gAMA = some` case) -/

set_option maxHeartbeats 1600000 in
/-- The metadata-aware parser accepts the with-gamma byte stream and
returns the expected header, IDAT, and metadata (with the
`gamma` set from the `gAMA` witness). -/
theorem parsePngForDecode_multiIdatGammaContainerSpec_correct_of_some
    {w : GammaChunkWitness} (hw : s.gAMA = some w) :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  -- For length ≥ 1, parsePngSimple sees IHDR + gAMA chunk after IHDR — the
  -- third readChunk in parsePngSimple reads gAMA (not IDAT), so it returns
  -- none. Fall through to parsePngLoopFuelWithMetadata.
  have hSimpleNone : parsePngSimple s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimple
    -- Walk IHDR + gAMA (which appears at pos 33, but parsePngSimple expects IDAT).
    have hSig : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
    have hLen1 : (8 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size, s.gAMAWireSize_of_some hw]; omega
    have hLen2' : (33 : Nat) + 3 < s.bytes.size := by
      rw [bytes_size, s.gAMAWireSize_of_some hw]; omega
    have hRead1 := s.readChunk_p_ihdr hw hLen1
    have hRead2 := s.readChunk_p_gAMA hw hLen2'
    -- typ2 = gamaTypeBytes ≠ idatTypeBytes ⇒ parsePngSimple returns none.
    have hGammaNeIdat : (gamaTypeBytes != idatTypeBytes) = true := by decide
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
          hLen2', hRead2, hGammaNeIdat,
          bne_self_eq_false' (a := ihdrTypeBytes)]
  -- parsePngSimpleWithMetadata = none follows.
  have hSimpleMetaNone : parsePngSimpleWithMetadata s.bytes s.bytes_size_ge_8 = none := by
    unfold parsePngSimpleWithMetadata
    simp [hSimpleNone]
  -- Signature check passes.
  have hSigExtract : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
  have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
    rw [hSigExtract]; exact bne_self_eq_false' (a := pngSignature)
  -- Fuel sufficient for IHDR + gAMA + n IDATs + IEND.
  have hLoopFuel : s.idatChunks.length + 2 ≤ s.bytes.size := by
    rw [bytes_size, s.gAMAWireSize_of_some hw]
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

/-! ### Forward correctness — `gAMA = none` case via the multi-IDAT theorem -/

/-- When no `gAMA` chunk is present, the multi-IDAT-with-gamma spec
reduces to a plain `MultiIdatContainerSpec`, and the
`parsePngForDecode` correctness theorem follows from
`parsePngForDecode_multiIdatContainerSpec_correct`. -/
theorem parsePngForDecode_multiIdatGammaContainerSpec_correct_of_none
    (h : s.gAMA = none) :
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
`MultiIdatGammaContainerSpec` byte stream and returns the header,
concatenated IDAT data, and the expected metadata (with
`gamma` set from the `gAMA` witness when present). -/
theorem parsePngForDecode_multiIdatGammaContainerSpec_correct :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := s.expectedMetadata } := by
  rcases h : s.gAMA with _ | w
  · -- gAMA = none
    have hNone := s.parsePngForDecode_multiIdatGammaContainerSpec_correct_of_none h
    -- Byte-size proofs differ; parsePngForDecode is proof-irrelevant in its
    -- size hypothesis.
    exact hNone
  · -- gAMA = some w
    exact s.parsePngForDecode_multiIdatGammaContainerSpec_correct_of_some h

end MultiIdatGammaContainerSpec

end Lemmas

end Bitmaps
