import Bitmap.Lemmas.Png.ChunkValidation
import Bitmap.Lemmas.Png.EncodeDecodeBase

namespace Bitmaps

namespace Lemmas

open Png

/-! ## PNG container forward-correctness spec (Phase 3)

A declarative spec for the PNG container layer — the byte structure
above zlib/DEFLATE that the runtime `parsePng` accepts. Phase 3a (this
commit) covers the minimal-shape spec corresponding to `parsePngSimple`:
the 8-byte signature, one `IHDR` chunk, one `IDAT` chunk, and a final
empty `IEND` chunk. This is exactly the shape `encodeBitmap` produces
and the shape `parsePngSimple` validates in one pass.

A later commit will extend the spec to multiple `IDAT` chunks and
supported or tolerated ancillary chunks (`gAMA`, `pHYs`, `tEXt`, …), proving forward
correctness through `parsePngLoopFuel` and the existing
`ChunkValidation.lean` lemmas. -/

/-- Encode a `PngHeader` into the 13-byte IHDR data payload, inverse to
`parseIHDRData`. The header order is:

  bytes 0-3   : width (BE u32)
  bytes 4-7   : height (BE u32)
  byte  8     : bit depth
  byte  9     : color type
  byte  10    : compression method (always 0)
  byte  11    : filter method (always 0)
  byte  12    : interlace method (always 0) -/
def encodeIHDRData (h : PngHeader) : ByteArray :=
  u32be h.width ++ u32be h.height
    ++ ByteArray.mk #[u8 h.bitDepth, u8 h.colorType, u8 0, u8 0, u8 0]

/-- The simple-shape container spec: 8-byte signature, one IHDR, one
IDAT carrying `idatData` payload bytes, and one empty IEND. The header
is constrained to the supported subset (`bitDepth ∈ {8, 16}` and
`colorType ∈ {0, 2, 4, 6}`) so the runtime accepts it. -/
structure SimpleContainerSpec where
  header : PngHeader
  idatData : ByteArray
  /-- Bit depth is 1, 8, or 16 (the supported subset values for this
  proof scope). The runtime decoder accepts:
    * 1-bit only with `colorType = 0` (grayscale);
    * 8-bit and 16-bit with `colorType ∈ {0, 2, 4, 6}`.
  Joint validity is captured by `hCtBdSupported`. -/
  hBitDepth : header.bitDepth = 1 ∨ header.bitDepth = 8 ∨ header.bitDepth = 16
  hColorType :
    header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6
  /-- The PNG runtime's joint color-type × bit-depth validity check.
  Rules out 1-bit non-grayscale combinations. -/
  hCtBdSupported :
    pngColorTypeBitDepthSupported header.colorType header.bitDepth = true
  hInterlace : header.interlace = 0
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32

/-- The on-the-wire bytes of a simple container: the PNG signature
followed by IHDR, IDAT, IEND chunks (each with a CRC computed by
`mkChunkBytes`). -/
def SimpleContainerSpec.bytes (s : SimpleContainerSpec) : ByteArray :=
  pngSignature
    ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
    ++ mkChunkBytes idatTypeBytes s.idatData
    ++ mkChunkBytes iendTypeBytes ByteArray.empty

/-- The byte stream of any simple-container spec is at least 8 bytes long
(it carries the PNG signature). This is the size precondition required
by `parsePng`. -/
lemma SimpleContainerSpec.bytes_size_ge_8 (s : SimpleContainerSpec) :
    8 ≤ s.bytes.size := by
  unfold SimpleContainerSpec.bytes
  simp [pngSignature_size, ByteArray.size_append]
  omega

/-- The encoded IHDR data has exactly 13 bytes — 4 (width) + 4 (height) + 5
(bit depth + color type + compression + filter + interlace). -/
lemma encodeIHDRData_size (h : PngHeader) : (encodeIHDRData h).size = 13 := by
  unfold encodeIHDRData
  have hTail : (ByteArray.mk #[u8 h.bitDepth, u8 h.colorType, u8 0, u8 0, u8 0]).size = 5 := rfl
  simp [u32be_size, ByteArray.size_append, hTail]

/-- `encodeIHDRData` factors through
`ihdrTailDepth (u8 h.bitDepth) (u8 h.colorType)` — the bridge to the
IHDR machinery in `EncodeDecodeBase.lean`. -/
lemma encodeIHDRData_eq_via_ihdrTailDepth (h : PngHeader) :
    encodeIHDRData h = u32be h.width ++ u32be h.height ++
      ihdrTailDepth (u8 h.bitDepth) (u8 h.colorType) := by
  rfl

/-- The on-the-wire size of a chunk built by `mkChunkBytes`: 12-byte
overhead (4 length + 4 type + 4 CRC) plus the payload size. -/
lemma mkChunkBytes_size (typBytes data : ByteArray) (hType : typBytes.size = 4) :
    (mkChunkBytes typBytes data).size = data.size + 12 := by
  rw [mkChunkBytes_def]
  simp [ByteArray.size_append, u32be_size, hType]
  omega

/-- Discharge `pngColorTypeBitDepthSupported` for the {8, 16} subset
of bit depths × {0, 2, 4, 6} color types. The 1-bit case (which only
admits color type 0) is handled directly via `s.hCtBdSupported` in the
spec. -/
lemma pngColorTypeBitDepthSupported_of_subset
    {ct bd : Nat}
    (hBitDepth : bd = 8 ∨ bd = 16)
    (hColorType : ct = 0 ∨ ct = 2 ∨ ct = 4 ∨ ct = 6) :
    pngColorTypeBitDepthSupported ct bd = true := by
  rcases hBitDepth with h | h <;> rw [h] <;>
    rcases hColorType with h | h | h | h <;> rw [h] <;> decide

/-- IHDR round-trip generalised to any bit depth < 256. The lemma
`parseIHDRData_encodeIHDRData_8or16` is the specialisation to {8, 16}. -/
lemma parseIHDRData_encodeIHDRData_lt256 (h : PngHeader)
    (hWidth : h.width < 2 ^ 32) (hHeight : h.height < 2 ^ 32)
    (hBitDepth : h.bitDepth < 256)
    (hInterlace : h.interlace = 0) (hColorType : h.colorType < 256) :
    parseIHDRData (encodeIHDRData h) = some h := by
  rw [encodeIHDRData_eq_via_ihdrTailDepth h]
  unfold parseIHDRData
  have hSize :
      (u32be h.width ++ u32be h.height ++
        ihdrTailDepth (u8 h.bitDepth) (u8 h.colorType)).size = 13 :=
    ihdr_payload_size_depth h.width h.height (u8 h.bitDepth) (u8 h.colorType)
  have hWidthRead :=
    readU32BE_ihdr_width_depth h.width h.height
      (u8 h.bitDepth) (u8 h.colorType) hWidth
  have hHeightRead :=
    readU32BE_ihdr_height_depth h.width h.height
      (u8 h.bitDepth) (u8 h.colorType) hHeight
  have hTailExtract :=
    ihdr_payload_extract_tail_depth h.width h.height
      (u8 h.bitDepth) (u8 h.colorType)
  have hCT_ofNat : (u8 h.colorType).toNat = h.colorType := by
    simp [u8, Nat.mod_eq_of_lt hColorType]
  have hBD_ofNat : (u8 h.bitDepth).toNat = h.bitDepth := by
    simp [u8, Nat.mod_eq_of_lt hBitDepth]
  have hZero_ofNat : (u8 0).toNat = 0 := by decide
  simp [hSize, hWidthRead, hHeightRead, hTailExtract, hCT_ofNat, hBD_ofNat, hZero_ofNat]
  obtain ⟨w, ht, ct, bd, interlace⟩ := h
  simp at hInterlace
  cases hInterlace
  rfl

/-- IHDR round-trip restated for bit depth ∈ {8, 16}. Thin wrapper
around `parseIHDRData_encodeIHDRData_lt256`. -/
lemma parseIHDRData_encodeIHDRData_8or16 (h : PngHeader)
    (hWidth : h.width < 2 ^ 32) (hHeight : h.height < 2 ^ 32)
    (hBitDepth : h.bitDepth = 8 ∨ h.bitDepth = 16)
    (hInterlace : h.interlace = 0) (hColorType : h.colorType < 256) :
    parseIHDRData (encodeIHDRData h) = some h :=
  parseIHDRData_encodeIHDRData_lt256 h hWidth hHeight
    (by rcases hBitDepth with hbd | hbd <;> rw [hbd] <;> decide)
    hInterlace hColorType

/-- The total byte size of a simple-container's on-the-wire bytes: 8 (signature)
+ 25 (IHDR chunk: 13-byte payload + 12 bytes overhead) + (12 + idatData.size)
(IDAT chunk) + 12 (IEND chunk) = idatData.size + 57. -/
lemma SimpleContainerSpec.bytes_size (s : SimpleContainerSpec) :
    s.bytes.size = s.idatData.size + 57 := by
  -- The auto-simp `mkChunkBytes_{ihdr,idat,iend}` lemmas rewrite to the `mkChunk`
  -- form; restate the per-chunk sizes against that form so simp can apply them.
  have hIhdrSize : (mkChunk "IHDR" (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunk_size]; simp [encodeIHDRData_size, ihdr_utf8ByteSize]
  have hIdatSize : (mkChunk "IDAT" s.idatData).size = s.idatData.size + 12 := by
    rw [mkChunk_size]; simp [idat_utf8ByteSize]
  have hIendSize : (mkChunk "IEND" ByteArray.empty).size = 12 := by
    rw [mkChunk_size]; simp [iend_utf8ByteSize]
  unfold SimpleContainerSpec.bytes
  simp [pngSignature_size, ByteArray.size_append, hIhdrSize, hIdatSize, hIendSize]
  omega

/-! ### Spec-level re-association

The runtime represents `s.bytes` as a left-associated chain of `++`. For
proofs that drill into specific positions, it is more convenient to view
the same bytes as `pngSignature ++ (chunks...)`, where the rest is itself
a right-associated chain. The next lemma pivots between the two forms. -/

/-- Re-associate the chained appends in `s.bytes` so the signature is
isolated as the leftmost prefix. Used by the chunk-reading proofs. -/
lemma SimpleContainerSpec.bytes_eq_signature_then_chunks (s : SimpleContainerSpec) :
    s.bytes =
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes idatTypeBytes s.idatData ++
            mkChunkBytes iendTypeBytes ByteArray.empty)) := by
  unfold SimpleContainerSpec.bytes
  simp [ByteArray.append_assoc]

/-- The first 8 bytes of any simple-container spec are the PNG signature.
Proved by re-associating the chained appends so the leftmost prefix is
isolated, then applying `byteArray_extract_append_prefix`. -/
lemma SimpleContainerSpec.bytes_extract_signature (s : SimpleContainerSpec) :
    s.bytes.extract 0 8 = pngSignature := by
  unfold SimpleContainerSpec.bytes
  have hSigSize : pngSignature.size = 8 := pngSignature_size
  -- Re-associate the chained `++` so we have `pngSignature ++ rest`.
  rw [show
    pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
      ++ mkChunkBytes idatTypeBytes s.idatData
      ++ mkChunkBytes iendTypeBytes ByteArray.empty
    = pngSignature ++ (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
      ++ mkChunkBytes idatTypeBytes s.idatData
      ++ mkChunkBytes iendTypeBytes ByteArray.empty) from by
      simp [ByteArray.append_assoc]]
  rw [byteArray_extract_append_prefix
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
      ++ mkChunkBytes idatTypeBytes s.idatData
      ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (n := 8) (by simp [hSigSize])]
  rw [← hSigSize]
  exact ByteArray.extract_zero_size

/-! ### Spec-side helpers for chunk-reading proofs

The two lemmas below let downstream proofs treat `s.bytes` as
`pngSignature ++ chunks` and slice into the chunks region directly,
skipping past the signature. Phase 3d will use them to derive the three
`readChunk` results for IHDR, IDAT, and IEND chunks. -/

/-- Slicing into `s.bytes` past the 8-byte signature: extracting the range
`[8 + start, 8 + finish)` of `s.bytes` equals extracting `[start, finish)`
of the chunks-only suffix. The `8 + finish ≤ s.bytes.size` precondition
keeps the slice within bounds. -/
lemma SimpleContainerSpec.bytes_extract_skip_signature
    (s : SimpleContainerSpec) (start finish : Nat) (_h : 8 + finish ≤ s.bytes.size) :
    s.bytes.extract (8 + start) (8 + finish) =
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        (mkChunkBytes idatTypeBytes s.idatData ++
          mkChunkBytes iendTypeBytes ByteArray.empty)).extract start finish := by
  rw [s.bytes_eq_signature_then_chunks]
  have hSig : pngSignature.size = 8 := pngSignature_size
  have h' := ByteArray.extract_append_size_add
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty))
    (i := start) (j := finish)
  simpa [hSig] using h'

/-! ### Reduction to `parsePngSimple`

`parsePng` tries `parsePngSimple` first and returns its result whenever
that fast path succeeds. This reduction lemma lets downstream proofs
work against `parsePngSimple` and then lift to `parsePng` for free. -/

/-- If the simple-shape parser accepts a byte stream, the general parser
returns the same result. Reduces the full forward-correctness theorem
for any `SimpleContainerSpec` to a proof about `parsePngSimple` alone. -/
lemma parsePng_of_parsePngSimple {bytes : ByteArray} (hsize : 8 ≤ bytes.size)
    {hdr : PngHeader} {idat : ByteArray}
    (h : parsePngSimple bytes hsize = some (hdr, idat)) :
    parsePng bytes hsize = some (hdr, idat) := by
  unfold parsePng
  simp [h]

/-- The full forward-correctness theorem for the simple container shape
reduces to `parsePngSimple_simpleContainerSpec_correct` via the
`parsePng_of_parsePngSimple` wiring. -/
theorem parsePng_simpleContainerSpec_correct_of_simple (s : SimpleContainerSpec)
    (hSimple :
      parsePngSimple s.bytes s.bytes_size_ge_8 = some (s.header, s.idatData)) :
    parsePng s.bytes s.bytes_size_ge_8 = some (s.header, s.idatData) :=
  parsePng_of_parsePngSimple s.bytes_size_ge_8 hSimple

/-! ### Per-chunk readChunk lemmas

Three lemmas, one per chunk in `SimpleContainerSpec.bytes`, mirroring
the encoder-specific `readChunk_encodeBitmap_{ihdr,idat,iend}` lemmas
in `EncodeDecodeBase.lean`. Each builds on `bytes_extract_skip_signature`
to slice into the chunks region and then on the existing `mkChunk_extract_*`
lemmas to identify each chunk's segments. -/

/-- The IHDR chunk in a simple container has exactly 25 bytes (12 overhead
+ 13 IHDR data). -/
private lemma mkChunkBytes_ihdr_size (s : SimpleContainerSpec) :
    (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
  rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4)]
  rw [encodeIHDRData_size]

/-- The IDAT chunk in a simple container has `12 + s.idatData.size` bytes. -/
private lemma mkChunkBytes_idat_size (s : SimpleContainerSpec) :
    (mkChunkBytes idatTypeBytes s.idatData).size = s.idatData.size + 12 := by
  rw [mkChunkBytes_size _ _ (by rfl : idatTypeBytes.size = 4)]

/-- The IEND chunk in a simple container has exactly 12 bytes (12 overhead
+ 0 payload). -/
private lemma mkChunkBytes_iend_size :
    (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
  rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]
  simp

/-- Slicing into `s.bytes` past the 8-byte signature + 25-byte IHDR chunk
gives access to the `idatChunk ++ iendChunk` suffix. Used by the IDAT and
IEND chunk-read lemmas. -/
lemma SimpleContainerSpec.bytes_extract_skip_through_ihdr
    (s : SimpleContainerSpec) (start finish : Nat)
    (_h : 33 + finish ≤ s.bytes.size) :
    s.bytes.extract (33 + start) (33 + finish) =
      (mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty).extract start finish := by
  have hSig : pngSignature.size = 8 := pngSignature_size
  have hIhdr : (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 :=
    mkChunkBytes_ihdr_size s
  rw [s.bytes_eq_signature_then_chunks]
  have hRe :
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes idatTypeBytes s.idatData ++
            mkChunkBytes iendTypeBytes ByteArray.empty))
      = (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)) ++
          (mkChunkBytes idatTypeBytes s.idatData ++
            mkChunkBytes iendTypeBytes ByteArray.empty) := by
    simp [ByteArray.append_assoc]
  rw [hRe]
  have hPrefSize :
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 33 := by
    simp [ByteArray.size_append, pngSignature_size, mkChunk_size,
      encodeIHDRData_size, ihdr_utf8ByteSize]
  have h := ByteArray.extract_append_size_add
    (a := pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
    (b := mkChunkBytes idatTypeBytes s.idatData ++
      mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  simpa [hPrefSize] using h

/-- The IHDR chunk in `s.bytes` lives at byte 8, has 13 bytes of payload, and
ends at byte 33. After applying `mkChunkBytes` to the encoded IHDR data,
the on-the-wire length-prefix-CRC layout is `u32be 13 ++ ihdrTypeBytes ++
encodeIHDRData s.header ++ u32be (crc32 ...).toNat`. -/
lemma readChunk_simpleContainer_ihdr (s : SimpleContainerSpec)
    (hLen : 8 + 3 < s.bytes.size) :
    readChunk s.bytes 8 hLen =
      some (ihdrTypeBytes, encodeIHDRData s.header, 33) := by
  have hSize : s.bytes.size = s.idatData.size + 57 := s.bytes_size
  -- IHDR length read at position 8 returns 13 (the IHDR data size).
  have hExtractLen : s.bytes.extract 8 12 = u32be 13 := by
    have h := s.bytes_extract_skip_signature 0 4 (by rw [hSize]; omega)
    simp only [Nat.add_zero] at h
    rw [h]
    -- chunks region [0..4] = first 4 bytes of ihdrChunk
    have hLeft := byteArray_extract_append_prefix
      (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
      (b := mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty)
      (n := 4)
      (by rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4),
              encodeIHDRData_size]; omega)
    rw [hLeft]
    -- mkChunkBytes ihdrTypeBytes ... = mkChunk "IHDR" ... by simp
    have hChunkLen : (mkChunk "IHDR" (encodeIHDRData s.header)).extract 0 4
        = u32be (encodeIHDRData s.header).size :=
      mkChunk_extract_len "IHDR" (encodeIHDRData s.header)
    simp [hChunkLen, encodeIHDRData_size]
  have hLenRead : readU32BE s.bytes 8 hLen = 13 :=
    readU32BE_of_extract_eq s.bytes 8 13 hLen hExtractLen (by decide)
  -- CRC end position bound.
  have hCrcEnd : 8 + 8 + 13 + 4 ≤ s.bytes.size := by rw [hSize]; omega
  -- IHDR type bytes at positions 12..16.
  have hExtractType : s.bytes.extract 12 16 = ihdrTypeBytes := by
    have h := s.bytes_extract_skip_signature 4 8 (by rw [hSize]; omega)
    rw [show (8 + 4 : Nat) = 12 by rfl, show (8 + 8 : Nat) = 16 by rfl] at h
    rw [h]
    -- chunks region [4..8] = bytes 4..8 of ihdrChunk
    have hLeft := byteArray_extract_append_left
      (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
      (b := mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty)
      (i := 4) (j := 8)
      (by rw [mkChunkBytes_ihdr_size]; omega)
      (by rw [mkChunkBytes_ihdr_size]; omega)
    rw [hLeft]
    show (mkChunk "IHDR" (encodeIHDRData s.header)).extract 4 8 = ihdrTypeBytes
    rw [mkChunk_extract_type "IHDR" (encodeIHDRData s.header) ihdr_utf8ByteSize]
    rfl
  -- IHDR data bytes at positions 16..29.
  have hExtractData : s.bytes.extract 16 (16 + 13) = encodeIHDRData s.header := by
    have h := s.bytes_extract_skip_signature 8 (8 + 13) (by rw [hSize]; omega)
    rw [show (8 + 8 : Nat) = 16 by rfl, show (8 + (8 + 13) : Nat) = 16 + 13 by rfl] at h
    rw [h]
    have hLeft := byteArray_extract_append_left
      (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
      (b := mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty)
      (i := 8) (j := 8 + 13)
      (by rw [mkChunkBytes_ihdr_size]; omega)
      (by rw [mkChunkBytes_ihdr_size]; omega)
    rw [hLeft]
    have hData := mkChunk_extract_data "IHDR" (encodeIHDRData s.header) ihdr_utf8ByteSize
    simp [encodeIHDRData_size] at hData
    simpa [encodeIHDRData_size] using hData
  -- IHDR CRC at positions 29..33.
  have hExtractCrc :
      s.bytes.extract 29 33 = u32be (crc32Chunk ihdrTypeBytes (encodeIHDRData s.header)).toNat := by
    have h := s.bytes_extract_skip_signature 21 25 (by rw [hSize]; omega)
    rw [show (8 + 21 : Nat) = 29 by rfl, show (8 + 25 : Nat) = 33 by rfl] at h
    rw [h]
    have hLeft := byteArray_extract_append_left
      (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
      (b := mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty)
      (i := 21) (j := 25)
      (by rw [mkChunkBytes_ihdr_size]; omega)
      (by rw [mkChunkBytes_ihdr_size])
    rw [hLeft]
    have hCrc := mkChunk_extract_crc "IHDR" (encodeIHDRData s.header) ihdr_utf8ByteSize
    simpa [encodeIHDRData_size, ihdrTypeBytes] using hCrc
  -- CRC value: readU32BE s.bytes 29 _ = computed CRC.
  have hCrcRead :
      readU32BE s.bytes (8 + 8 + 13) (by omega) =
        (crc32Chunk ihdrTypeBytes (encodeIHDRData s.header)).toNat :=
    readU32BE_of_extract_eq s.bytes 29 _ (by omega) hExtractCrc (UInt32.toNat_lt _)
  -- Combine via readChunk's definition.
  unfold readChunk
  simp [hLenRead, hCrcEnd, hExtractType, hExtractData, hCrcRead]

/-- The IDAT chunk in `s.bytes` lives at byte 33, has `s.idatData.size` bytes
of payload, and ends at byte `45 + s.idatData.size`. The `hIdatSize`
precondition reflects the PNG spec's u32 length field — the runtime
decoder will only succeed on inputs whose IDAT chunk size fits in 32 bits. -/
lemma readChunk_simpleContainer_idat (s : SimpleContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hLen : 33 + 3 < s.bytes.size) :
    readChunk s.bytes 33 hLen =
      some (idatTypeBytes, s.idatData, 45 + s.idatData.size) := by
  have hSize : s.bytes.size = s.idatData.size + 57 := s.bytes_size
  -- IDAT length read at position 33 returns s.idatData.size.
  have hExtractLen : s.bytes.extract 33 (33 + 4) = u32be s.idatData.size := by
    have h := s.bytes_extract_skip_through_ihdr 0 4 (by rw [hSize]; omega)
    simp only [Nat.add_zero] at h
    rw [h]
    have hLeft := byteArray_extract_append_prefix
      (a := mkChunkBytes idatTypeBytes s.idatData)
      (b := mkChunkBytes iendTypeBytes ByteArray.empty)
      (n := 4) (by rw [mkChunkBytes_idat_size]; omega)
    rw [hLeft]
    show (mkChunk "IDAT" s.idatData).extract 0 4 = u32be s.idatData.size
    rw [mkChunk_extract_len "IDAT" s.idatData]
  have hLenRead : readU32BE s.bytes 33 hLen = s.idatData.size :=
    readU32BE_of_extract_eq s.bytes 33 s.idatData.size hLen hExtractLen hIdatSize
  -- CRC end position bound.
  have hCrcEnd : 33 + 8 + s.idatData.size + 4 ≤ s.bytes.size := by rw [hSize]; omega
  -- IDAT type bytes at positions 37..41.
  have hExtractType : s.bytes.extract 37 41 = idatTypeBytes := by
    have h := s.bytes_extract_skip_through_ihdr 4 8 (by rw [hSize]; omega)
    rw [show (33 + 4 : Nat) = 37 by rfl, show (33 + 8 : Nat) = 41 by rfl] at h
    rw [h]
    have hLeft := byteArray_extract_append_left
      (a := mkChunkBytes idatTypeBytes s.idatData)
      (b := mkChunkBytes iendTypeBytes ByteArray.empty)
      (i := 4) (j := 8)
      (by rw [mkChunkBytes_idat_size]; omega)
      (by rw [mkChunkBytes_idat_size]; omega)
    rw [hLeft]
    show (mkChunk "IDAT" s.idatData).extract 4 8 = idatTypeBytes
    rw [mkChunk_extract_type "IDAT" s.idatData idat_utf8ByteSize]
    rfl
  -- IDAT data bytes at positions 41..(41 + s.idatData.size).
  have hExtractData : s.bytes.extract 41 (41 + s.idatData.size) = s.idatData := by
    have h := s.bytes_extract_skip_through_ihdr 8 (8 + s.idatData.size) (by rw [hSize]; omega)
    rw [show (33 + 8 : Nat) = 41 by rfl,
        show (33 + (8 + s.idatData.size) : Nat) = 41 + s.idatData.size by omega] at h
    rw [h]
    have hLeft := byteArray_extract_append_left
      (a := mkChunkBytes idatTypeBytes s.idatData)
      (b := mkChunkBytes iendTypeBytes ByteArray.empty)
      (i := 8) (j := 8 + s.idatData.size)
      (by rw [mkChunkBytes_idat_size]; omega)
      (by rw [mkChunkBytes_idat_size]; omega)
    rw [hLeft]
    have hData := mkChunk_extract_data "IDAT" s.idatData idat_utf8ByteSize
    simpa using hData
  -- IDAT CRC at positions (41 + s.idatData.size)..(45 + s.idatData.size).
  have hExtractCrc :
      s.bytes.extract (41 + s.idatData.size) (45 + s.idatData.size) =
        u32be (crc32Chunk idatTypeBytes s.idatData).toNat := by
    have h := s.bytes_extract_skip_through_ihdr (8 + s.idatData.size) (12 + s.idatData.size)
      (by rw [hSize]; omega)
    rw [show (33 + (8 + s.idatData.size) : Nat) = 41 + s.idatData.size by omega,
        show (33 + (12 + s.idatData.size) : Nat) = 45 + s.idatData.size by omega] at h
    rw [h]
    have hLeft := byteArray_extract_append_left
      (a := mkChunkBytes idatTypeBytes s.idatData)
      (b := mkChunkBytes iendTypeBytes ByteArray.empty)
      (i := 8 + s.idatData.size) (j := 12 + s.idatData.size)
      (by rw [mkChunkBytes_idat_size]; omega)
      (by rw [mkChunkBytes_idat_size]; omega)
    rw [hLeft]
    have hCrc := mkChunk_extract_crc "IDAT" s.idatData idat_utf8ByteSize
    simpa [idatTypeBytes] using hCrc
  -- CRC value: readU32BE s.bytes (41 + s.idatData.size) _ = computed CRC.
  have hCrcRead :
      readU32BE s.bytes (33 + 8 + s.idatData.size) (by omega) =
        (crc32Chunk idatTypeBytes s.idatData).toNat :=
    readU32BE_of_extract_eq s.bytes (41 + s.idatData.size) _
      (by omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExtractCrc)
      (UInt32.toNat_lt _)
  -- Combine via readChunk's definition.
  unfold readChunk
  simp [hLenRead, hCrcEnd, hExtractType, hExtractData, hCrcRead]
  -- The end position should be 45 + s.idatData.size.
  show (33 + 8 + s.idatData.size + 4 : Nat) = 45 + s.idatData.size
  omega

/-- Slicing into `s.bytes` past the 8-byte signature + 25-byte IHDR chunk +
`(12 + s.idatData.size)`-byte IDAT chunk gives access to the IEND
chunk's bytes at offset `45 + s.idatData.size`. -/
lemma SimpleContainerSpec.bytes_extract_skip_through_idat
    (s : SimpleContainerSpec) (start finish : Nat)
    (_h : 45 + s.idatData.size + finish ≤ s.bytes.size) :
    s.bytes.extract (45 + s.idatData.size + start) (45 + s.idatData.size + finish) =
      (mkChunkBytes iendTypeBytes ByteArray.empty).extract start finish := by
  have hSig : pngSignature.size = 8 := pngSignature_size
  have hIhdr := mkChunkBytes_ihdr_size s
  have hIdat := mkChunkBytes_idat_size s
  rw [s.bytes_eq_signature_then_chunks]
  have hRe :
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes idatTypeBytes s.idatData ++
            mkChunkBytes iendTypeBytes ByteArray.empty))
      = (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          mkChunkBytes idatTypeBytes s.idatData) ++
          mkChunkBytes iendTypeBytes ByteArray.empty := by
    simp [ByteArray.append_assoc]
  rw [hRe]
  have hPrefSize :
      pngSignature.size + (mkChunk "IHDR" (encodeIHDRData s.header)).size +
        (mkChunk "IDAT" s.idatData).size = 45 + s.idatData.size := by
    simp [pngSignature_size, mkChunk_size, encodeIHDRData_size,
      ihdr_utf8ByteSize, idat_utf8ByteSize]
    omega
  have h := ByteArray.extract_append_size_add
    (a := pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      mkChunkBytes idatTypeBytes s.idatData)
    (b := mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  simp [ByteArray.size_append] at h
  rw [hPrefSize] at h
  exact h

/-- The IEND chunk in `s.bytes` lives at byte `45 + s.idatData.size`, has 0
bytes of payload, and ends at byte `57 + s.idatData.size` (the end of
the file). -/
lemma readChunk_simpleContainer_iend (s : SimpleContainerSpec)
    (hLen : (45 + s.idatData.size) + 3 < s.bytes.size) :
    readChunk s.bytes (45 + s.idatData.size) hLen =
      some (iendTypeBytes, ByteArray.empty, 57 + s.idatData.size) := by
  have hSize : s.bytes.size = s.idatData.size + 57 := s.bytes_size
  -- IEND length read returns 0.
  have hExtractLen :
      s.bytes.extract (45 + s.idatData.size) (45 + s.idatData.size + 4) = u32be 0 := by
    have h := s.bytes_extract_skip_through_idat 0 4 (by rw [hSize]; omega)
    simp only [Nat.add_zero] at h
    rw [h]
    show (mkChunk "IEND" ByteArray.empty).extract 0 4 = u32be 0
    rw [mkChunk_extract_len "IEND" ByteArray.empty]
    simp
  have hLenRead :
      readU32BE s.bytes (45 + s.idatData.size)
        (by rw [hSize]; omega) = 0 :=
    readU32BE_of_extract_eq s.bytes (45 + s.idatData.size) 0
      (by rw [hSize]; omega) hExtractLen (by decide)
  -- CRC end position bound.
  have hCrcEnd :
      (45 + s.idatData.size) + 8 + 0 + 4 ≤ s.bytes.size := by rw [hSize]; omega
  -- IEND type bytes at positions (49 + s.idatData.size)..(53 + s.idatData.size).
  have hExtractType :
      s.bytes.extract ((45 + s.idatData.size) + 4) ((45 + s.idatData.size) + 8) =
        iendTypeBytes := by
    have h := s.bytes_extract_skip_through_idat 4 8 (by rw [hSize]; omega)
    rw [h]
    show (mkChunk "IEND" ByteArray.empty).extract 4 8 = iendTypeBytes
    rw [mkChunk_extract_type "IEND" ByteArray.empty iend_utf8ByteSize]
    rfl
  -- IEND data bytes at position (53 + s.idatData.size)..(53 + s.idatData.size) (empty).
  have hExtractData :
      s.bytes.extract ((45 + s.idatData.size) + 8) ((45 + s.idatData.size) + 8 + 0) =
        ByteArray.empty := by
    have h := s.bytes_extract_skip_through_idat 8 (8 + 0) (by rw [hSize]; omega)
    rw [show (45 + s.idatData.size + (8 + 0) : Nat) = (45 + s.idatData.size) + 8 + 0 by omega] at h
    rw [h]
    have hData := mkChunk_extract_data "IEND" ByteArray.empty iend_utf8ByteSize
    simpa using hData
  -- IEND CRC.
  have hExtractCrc :
      s.bytes.extract ((45 + s.idatData.size) + 8) ((45 + s.idatData.size) + 8 + 4) =
        u32be (crc32Chunk iendTypeBytes ByteArray.empty).toNat := by
    have h := s.bytes_extract_skip_through_idat 8 12 (by rw [hSize]; omega)
    rw [show (45 + s.idatData.size + 12 : Nat) = (45 + s.idatData.size) + 8 + 4 by omega] at h
    rw [h]
    have hCrc := mkChunk_extract_crc "IEND" ByteArray.empty iend_utf8ByteSize
    simpa [iendTypeBytes] using hCrc
  have hCrcRead :
      readU32BE s.bytes ((45 + s.idatData.size) + 8 + 0) (by omega) =
        (crc32Chunk iendTypeBytes ByteArray.empty).toNat :=
    readU32BE_of_extract_eq s.bytes ((45 + s.idatData.size) + 8) _
      (by omega) (by simpa using hExtractCrc) (UInt32.toNat_lt _)
  -- Combine via readChunk's definition.
  unfold readChunk
  simp [hLenRead, hCrcEnd, hExtractType, hExtractData, hCrcRead]
  show ((45 + s.idatData.size) + 8 + 0 + 4 : Nat) = 57 + s.idatData.size
  omega

/-! ### Forward correctness through `parsePngSimple`

Compose the three per-chunk readChunk lemmas with the IHDR round trip
and the supported-subset constraints from `SimpleContainerSpec` to
prove that `parsePngSimple` accepts `s.bytes` and returns
`(s.header, s.idatData)`. Combined with `parsePng_of_parsePngSimple`,
this closes the Phase 3 final theorem. -/

/-- Forward correctness for the simple-shape container parser:
`parsePngSimple` accepts `s.bytes` and returns `(s.header, s.idatData)`,
given the spec's constraints plus the standard PNG u32 length-field
fit (`s.idatData.size < 2^32`). -/
theorem parsePngSimple_simpleContainerSpec_correct (s : SimpleContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32) :
    parsePngSimple s.bytes s.bytes_size_ge_8 = some (s.header, s.idatData) := by
  unfold parsePngSimple
  have hSize : s.bytes.size = s.idatData.size + 57 := s.bytes_size
  have hSig : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
  -- Position bounds for the three chunk reads.
  have hLen1 : (8 : Nat) + 3 < s.bytes.size := by rw [hSize]; omega
  have hLen2 : (33 : Nat) + 3 < s.bytes.size := by rw [hSize]; omega
  have hLen3 : (45 + s.idatData.size : Nat) + 3 < s.bytes.size := by rw [hSize]; omega
  -- The three chunk reads.
  have hRead1 := readChunk_simpleContainer_ihdr s hLen1
  have hRead2 := readChunk_simpleContainer_idat s hIdatSize hLen2
  have hRead3 := readChunk_simpleContainer_iend s hLen3
  -- Color type < 256 (from being in {0, 2, 6}).
  have hCT256 : s.header.colorType < 256 := by
    rcases s.hColorType with h0 | hrest
    · rw [h0]; decide
    rcases hrest with h2 | hrest
    · rw [h2]; decide
    rcases hrest with h4 | h6
    · rw [h4]; decide
    · rw [h6]; decide
  -- IHDR data round-trip parses to the original header.
  have hBDlt : s.header.bitDepth < 256 := by
    rcases s.hBitDepth with h | h | h <;> rw [h] <;> decide
  have hParseHdr :=
    parseIHDRData_encodeIHDRData_lt256 s.header s.hWidth s.hHeight hBDlt s.hInterlace hCT256
  -- Color type IS in {0, 2, 6}, so the bad-color-type check fails.
  have hCTok :
      (s.header.colorType != 0 && s.header.colorType != 2 &&
        s.header.colorType != 4 && s.header.colorType != 6)
        = false := by
    rcases s.hColorType with h0 | hrest
    · rw [h0]; decide
    rcases hrest with h2 | hrest
    · rw [h2]; decide
    rcases hrest with h4 | h6
    · rw [h4]; decide
    · rw [h6]; decide
  have hCtBdOk :
      pngColorTypeBitDepthSupported s.header.colorType s.header.bitDepth = true :=
    s.hCtBdSupported
  -- IEND data is empty, so the non-empty-IEND check fails.
  have hEmpty : (ByteArray.empty.size != 0) = false := by decide
  -- Final position (57 + s.idatData.size) equals s.bytes.size, so the
  -- trailing-bytes check fails.
  have hFinal : ((57 + s.idatData.size) != s.bytes.size) = false := by
    rw [hSize]; simp; omega
  have hCTProp :
      ¬s.header.colorType = 0 → ¬s.header.colorType = 2 →
        ¬s.header.colorType = 4 → s.header.colorType = 6 := by
    intro h0 h2 h4
    rcases s.hColorType with hc0 | hrest
    · exact (h0 hc0).elim
    rcases hrest with hc2 | hrest
    · exact (h2 hc2).elim
    rcases hrest with hc4 | hc6
    · exact (h4 hc4).elim
    · exact hc6
  -- Combine all branches via simp.
  simp [hSig, hLen1, hRead1, hParseHdr, hCtBdOk,
    hLen2, hRead2, hLen3, hRead3, hFinal]
  exact
    ⟨bne_self_eq_false' (a := pngSignature),
      bne_self_eq_false' (a := ihdrTypeBytes),
      hCTProp,
      bne_self_eq_false' (a := idatTypeBytes),
      bne_self_eq_false' (a := iendTypeBytes)⟩

/-- The full Phase 3 forward-correctness theorem: `parsePng` accepts any
byte stream matching `SimpleContainerSpec` and returns the spec's header
and IDAT data. Composes `parsePngSimple_simpleContainerSpec_correct`
with the `parsePng → parsePngSimple` reduction. -/
theorem parsePng_simpleContainerSpec_correct (s : SimpleContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32) :
    parsePng s.bytes s.bytes_size_ge_8 = some (s.header, s.idatData) :=
  parsePng_simpleContainerSpec_correct_of_simple s
    (parsePngSimple_simpleContainerSpec_correct s hIdatSize)

end Lemmas

end Bitmaps
