import Bitmap.Lemmas.Png.ContainerSpec

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette PNG container scaffold

This module captures the minimal container shape for an indexed-palette PNG:
signature, IHDR, required PLTE, one IDAT, and IEND.  The first facts prove the
wire-size arithmetic and the PLTE payload acceptance needed by later parser
forward-correctness proofs. -/

/-- The indexed-palette container shape: PNG signature, IHDR, required PLTE,
one IDAT, and IEND.  It carries the validation facts needed by the runtime
parser before proving the full parser loop over this byte stream. -/
structure PaletteContainerSpec where
  header : PngHeader
  palette : PngPalette
  idatData : ByteArray
  /-- PNG indexed bit depth is one of the supported packed depths. -/
  hBitDepth :
    header.bitDepth = 1 ∨ header.bitDepth = 2 ∨
      header.bitDepth = 4 ∨ header.bitDepth = 8
  /-- This scaffold is specifically for indexed-color PNGs. -/
  hColorType : header.colorType = 3
  /-- The runtime accepts this color type and bit-depth pair. -/
  hCtBdSupported :
    pngColorTypeBitDepthSupported header.colorType header.bitDepth = true
  /-- Interlace method is valid for the parser. -/
  hInterlace : header.interlace = 0 ∨ header.interlace = 1
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32
  /-- PLTE must contain at least one RGB triplet. -/
  hPaletteNonempty : palette.entries.size ≠ 0
  /-- PLTE bytes are RGB triplets. -/
  hPaletteTriplets : palette.entries.size % 3 = 0
  /-- PNG palettes have at most 256 entries. -/
  hPaletteMax : palette.entries.size ≤ 256 * 3
  /-- The PLTE entry count fits the selected bit depth. -/
  hPaletteFits :
    palette.entryCount ≤ paletteMaxEntriesForBitDepth header.bitDepth

/-- On-the-wire bytes for the indexed palette scaffold. -/
def PaletteContainerSpec.bytes (s : PaletteContainerSpec) : ByteArray :=
  pngSignature
    ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
    ++ mkChunkBytes plteTypeBytes s.palette.entries
    ++ mkChunkBytes idatTypeBytes s.idatData
    ++ mkChunkBytes iendTypeBytes ByteArray.empty

/-- Palette container bytes always carry at least the PNG signature.
This discharges the outer parser size precondition for later proofs. -/
lemma PaletteContainerSpec.bytes_size_ge_8 (s : PaletteContainerSpec) :
    8 ≤ s.bytes.size := by
  unfold PaletteContainerSpec.bytes
  simp [pngSignature_size, ByteArray.size_append]
  omega

/-- Exact byte size of the indexed-palette scaffold.
This pins down the chunk overhead before parser-position proofs. -/
lemma PaletteContainerSpec.bytes_size (s : PaletteContainerSpec) :
    s.bytes.size = s.idatData.size + s.palette.entries.size + 69 := by
  have hIhdrSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    have ht : ihdrTypeBytes.size = 4 := by rfl
    have hs := mkChunkBytes_size ihdrTypeBytes (encodeIHDRData s.header) ht
    simpa [encodeIHDRData_size] using hs
  have hPlteSize :
      (mkChunkBytes plteTypeBytes s.palette.entries).size =
        s.palette.entries.size + 12 := by
    have ht : plteTypeBytes.size = 4 := by rfl
    simpa using mkChunkBytes_size plteTypeBytes s.palette.entries ht
  have hIdatSize :
      (mkChunkBytes idatTypeBytes s.idatData).size =
        s.idatData.size + 12 := by
    have ht : idatTypeBytes.size = 4 := by rfl
    simpa using mkChunkBytes_size idatTypeBytes s.idatData ht
  have hIendSize : (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    have ht : iendTypeBytes.size = 4 := by rfl
    have hs := mkChunkBytes_size iendTypeBytes ByteArray.empty ht
    simpa using hs
  unfold PaletteContainerSpec.bytes
  simp only [ByteArray.size_append, pngSignature_size, hIhdrSize, hPlteSize,
    hIdatSize, hIendSize]
  omega

/-- The scaffold PLTE payload is accepted by `parsePlteData`.
This bridges the container-level palette invariant to chunk validation. -/
lemma PaletteContainerSpec.parsePlteData (s : PaletteContainerSpec) :
    parsePlteData s.header s.palette.entries = some s.palette := by
  have hfits :
      s.header.colorType = 3 →
        s.palette.entries.size / 3 ≤
          paletteMaxEntriesForBitDepth s.header.bitDepth := by
    intro _
    simpa [PngPalette.entryCount] using s.hPaletteFits
  have hparse :=
    parsePlteData_accepts_valid s.header s.palette.entries
      s.hPaletteNonempty s.hPaletteTriplets s.hPaletteMax hfits
  have hpal : ({ entries := s.palette.entries } : PngPalette) = s.palette := by
    cases s.palette
    rfl
  simpa [hpal] using hparse

namespace PaletteContainerSpec

/-- Re-associate `bytes` so the PNG signature is isolated.
This is the common starting point for all palette chunk-position proofs. -/
lemma bytes_eq_signature_then_chunks (s : PaletteContainerSpec) :
    s.bytes =
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes plteTypeBytes s.palette.entries ++
            (mkChunkBytes idatTypeBytes s.idatData ++
              mkChunkBytes iendTypeBytes ByteArray.empty))) := by
  unfold PaletteContainerSpec.bytes
  simp [ByteArray.append_assoc]

/-- The first eight bytes of the scaffold are the PNG signature.
This is the signature-side fact used before chunk parsing begins. -/
lemma bytes_extract_signature (s : PaletteContainerSpec) :
    s.bytes.extract 0 8 = pngSignature := by
  rw [bytes_eq_signature_then_chunks s]
  have hSigSize : pngSignature.size = 8 := pngSignature_size
  rw [byteArray_extract_append_prefix
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (mkChunkBytes plteTypeBytes s.palette.entries ++
        (mkChunkBytes idatTypeBytes s.idatData ++
          mkChunkBytes iendTypeBytes ByteArray.empty)))
    (n := 8) (by simp [hSigSize])]
  rw [← hSigSize]
  exact ByteArray.extract_zero_size

/-- IHDR chunk wire size inside the indexed-palette scaffold.
This supports the fixed byte offset of the following PLTE chunk. -/
private lemma ihdrChunk_size (s : PaletteContainerSpec) :
    (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
  rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4)]
  rw [encodeIHDRData_size]

/-- PLTE chunk wire size inside the indexed-palette scaffold.
This supports the byte offset of the following IDAT chunk. -/
private lemma plteChunk_size (s : PaletteContainerSpec) :
    (mkChunkBytes plteTypeBytes s.palette.entries).size =
      s.palette.entries.size + 12 := by
  rw [mkChunkBytes_size _ _ (by rfl : plteTypeBytes.size = 4)]

/-- IDAT chunk wire size inside the indexed-palette scaffold.
This supports the byte offset of the final IEND chunk. -/
private lemma idatChunk_size (s : PaletteContainerSpec) :
    (mkChunkBytes idatTypeBytes s.idatData).size = s.idatData.size + 12 := by
  rw [mkChunkBytes_size _ _ (by rfl : idatTypeBytes.size = 4)]

/-- IEND chunk wire size inside the indexed-palette scaffold.
This pins the final empty chunk's wrapped size. -/
private lemma iendChunk_size :
    (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
  rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]
  simp

/-- Slicing past the 8-byte signature exposes the chunk-only suffix.
Later chunk proofs use this to reason relative to chunk offsets. -/
lemma bytes_extract_skip_signature (s : PaletteContainerSpec)
    (start finish : Nat) (_h : 8 + finish ≤ s.bytes.size) :
    s.bytes.extract (8 + start) (8 + finish) =
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        (mkChunkBytes plteTypeBytes s.palette.entries ++
          (mkChunkBytes idatTypeBytes s.idatData ++
            mkChunkBytes iendTypeBytes ByteArray.empty))).extract start finish := by
  rw [bytes_eq_signature_then_chunks s]
  have hSig : pngSignature.size = 8 := pngSignature_size
  have h := ByteArray.extract_append_size_add
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (mkChunkBytes plteTypeBytes s.palette.entries ++
        (mkChunkBytes idatTypeBytes s.idatData ++
          mkChunkBytes iendTypeBytes ByteArray.empty)))
    (i := start) (j := finish)
  simpa [hSig] using h

/-- Slicing past the signature and IHDR exposes `PLTE ++ IDAT ++ IEND`.
This is the PLTE-relative view used for palette chunk parsing. -/
lemma bytes_extract_skip_through_ihdr (s : PaletteContainerSpec)
    (start finish : Nat) (_h : 33 + finish ≤ s.bytes.size) :
    s.bytes.extract (33 + start) (33 + finish) =
      (mkChunkBytes plteTypeBytes s.palette.entries ++
        (mkChunkBytes idatTypeBytes s.idatData ++
          mkChunkBytes iendTypeBytes ByteArray.empty)).extract start finish := by
  rw [bytes_eq_signature_then_chunks s]
  have hRe :
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes plteTypeBytes s.palette.entries ++
            (mkChunkBytes idatTypeBytes s.idatData ++
              mkChunkBytes iendTypeBytes ByteArray.empty)))
      =
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)) ++
        (mkChunkBytes plteTypeBytes s.palette.entries ++
          (mkChunkBytes idatTypeBytes s.idatData ++
            mkChunkBytes iendTypeBytes ByteArray.empty)) := by
    simp [ByteArray.append_assoc]
  rw [hRe]
  have hIhdrMk :
      (mkChunk "IHDR" (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunk_size]
    simp [encodeIHDRData_size, ihdr_utf8ByteSize]
  have hPref :
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 33 := by
    simp [ByteArray.size_append, pngSignature_size, hIhdrMk]
  have h := ByteArray.extract_append_size_add
    (a := pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
    (b := mkChunkBytes plteTypeBytes s.palette.entries ++
      (mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty))
    (i := start) (j := finish)
  simpa [hPref] using h

/-- Slicing past signature, IHDR, and PLTE exposes `IDAT ++ IEND`.
This is the IDAT-relative view for the indexed-palette scaffold. -/
lemma bytes_extract_skip_through_plte (s : PaletteContainerSpec)
    (start finish : Nat)
    (_h : 45 + s.palette.entries.size + finish ≤ s.bytes.size) :
    s.bytes.extract (45 + s.palette.entries.size + start)
        (45 + s.palette.entries.size + finish) =
      (mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty).extract start finish := by
  rw [bytes_eq_signature_then_chunks s]
  have hRe :
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes plteTypeBytes s.palette.entries ++
            (mkChunkBytes idatTypeBytes s.idatData ++
              mkChunkBytes iendTypeBytes ByteArray.empty)))
      =
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        mkChunkBytes plteTypeBytes s.palette.entries) ++
        (mkChunkBytes idatTypeBytes s.idatData ++
          mkChunkBytes iendTypeBytes ByteArray.empty) := by
    simp [ByteArray.append_assoc]
  rw [hRe]
  have hIhdrMk :
      (mkChunk "IHDR" (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunk_size]
    simp [encodeIHDRData_size, ihdr_utf8ByteSize]
  have hPref :
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        mkChunkBytes plteTypeBytes s.palette.entries).size =
        45 + s.palette.entries.size := by
    simp [ByteArray.size_append, pngSignature_size, hIhdrMk, plteChunk_size s]
    omega
  have h := ByteArray.extract_append_size_add
    (a := pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      mkChunkBytes plteTypeBytes s.palette.entries)
    (b := mkChunkBytes idatTypeBytes s.idatData ++
      mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  rw [hPref] at h
  exact h

/-- Slicing past signature, IHDR, PLTE, and IDAT exposes IEND.
This gives the final chunk-relative view for parser-position proofs. -/
lemma bytes_extract_skip_through_idat (s : PaletteContainerSpec)
    (start finish : Nat)
    (_h : 57 + s.palette.entries.size + s.idatData.size + finish ≤ s.bytes.size) :
    s.bytes.extract (57 + s.palette.entries.size + s.idatData.size + start)
        (57 + s.palette.entries.size + s.idatData.size + finish) =
      (mkChunkBytes iendTypeBytes ByteArray.empty).extract start finish := by
  rw [bytes_eq_signature_then_chunks s]
  have hRe :
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (mkChunkBytes plteTypeBytes s.palette.entries ++
            (mkChunkBytes idatTypeBytes s.idatData ++
              mkChunkBytes iendTypeBytes ByteArray.empty)))
      =
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        mkChunkBytes plteTypeBytes s.palette.entries ++
          mkChunkBytes idatTypeBytes s.idatData) ++
        mkChunkBytes iendTypeBytes ByteArray.empty := by
    simp [ByteArray.append_assoc]
  rw [hRe]
  have hIhdrMk :
      (mkChunk "IHDR" (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunk_size]
    simp [encodeIHDRData_size, ihdr_utf8ByteSize]
  have hIdatMk : (mkChunk "IDAT" s.idatData).size = s.idatData.size + 12 := by
    rw [mkChunk_size]
    simp [idat_utf8ByteSize]
  have hPref :
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        mkChunkBytes plteTypeBytes s.palette.entries ++
          mkChunkBytes idatTypeBytes s.idatData).size =
        57 + s.palette.entries.size + s.idatData.size := by
    simp [ByteArray.size_append, pngSignature_size, hIhdrMk, plteChunk_size s,
      hIdatMk]
    omega
  have h := ByteArray.extract_append_size_add
    (a := pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      mkChunkBytes plteTypeBytes s.palette.entries ++
        mkChunkBytes idatTypeBytes s.idatData)
    (b := mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  rw [hPref] at h
  exact h

/-- The IHDR chunk bytes live at byte offset 8.
This wraps the local IHDR extraction into a full wrapped-chunk fact. -/
lemma bytes_extract_ihdr (s : PaletteContainerSpec) :
    s.bytes.extract 8 (8 + 12 + (encodeIHDRData s.header).size) =
      mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) := by
  have hSize : 8 + (12 + (encodeIHDRData s.header).size) ≤ s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s, encodeIHDRData_size]
    omega
  have h := bytes_extract_skip_signature s 0 (12 + (encodeIHDRData s.header).size) hSize
  simp only [Nat.add_zero] at h
  rw [show (8 + 12 + (encodeIHDRData s.header).size : Nat) =
      8 + (12 + (encodeIHDRData s.header).size) by omega]
  rw [h]
  have hChunkSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size =
        12 + (encodeIHDRData s.header).size := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4)]
    omega
  rw [byteArray_extract_append_prefix
    (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
    (b := mkChunkBytes plteTypeBytes s.palette.entries ++
      (mkChunkBytes idatTypeBytes s.idatData ++
        mkChunkBytes iendTypeBytes ByteArray.empty))
    (n := 12 + (encodeIHDRData s.header).size)
    (by rw [hChunkSize])]
  rw [← hChunkSize]
  exact ByteArray.extract_zero_size

/-- The PLTE chunk bytes live immediately after IHDR at byte offset 33.
This is the wrapped-chunk fact used by `readChunk_plte`. -/
lemma bytes_extract_plte (s : PaletteContainerSpec) :
    s.bytes.extract 33 (33 + 12 + s.palette.entries.size) =
      mkChunkBytes plteTypeBytes s.palette.entries := by
  have hSize : 33 + (12 + s.palette.entries.size) ≤ s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s]
    omega
  have h := bytes_extract_skip_through_ihdr s 0
    (12 + s.palette.entries.size) hSize
  simp only [Nat.add_zero] at h
  rw [show (33 + (12 + s.palette.entries.size) : Nat) =
      33 + 12 + s.palette.entries.size by omega] at h
  rw [h]
  have hChunkSize :
      (mkChunkBytes plteTypeBytes s.palette.entries).size =
        12 + s.palette.entries.size := by
    rw [mkChunkBytes_size _ _ (by rfl : plteTypeBytes.size = 4)]
    omega
  rw [byteArray_extract_append_prefix
    (a := mkChunkBytes plteTypeBytes s.palette.entries)
    (b := mkChunkBytes idatTypeBytes s.idatData ++
      mkChunkBytes iendTypeBytes ByteArray.empty)
    (n := 12 + s.palette.entries.size)
    (by rw [hChunkSize])]
  rw [← hChunkSize]
  exact ByteArray.extract_zero_size

/-- The IDAT chunk bytes live after the PLTE chunk.
This is the wrapped-chunk fact used by `readChunk_idat`. -/
lemma bytes_extract_idat (s : PaletteContainerSpec) :
    s.bytes.extract (45 + s.palette.entries.size)
        (45 + s.palette.entries.size + 12 + s.idatData.size) =
      mkChunkBytes idatTypeBytes s.idatData := by
  have hSize :
      45 + s.palette.entries.size + (12 + s.idatData.size) ≤ s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s]
    omega
  have h := bytes_extract_skip_through_plte s 0
    (12 + s.idatData.size) hSize
  simp only [Nat.add_zero] at h
  rw [show (45 + s.palette.entries.size + (12 + s.idatData.size) : Nat) =
      45 + s.palette.entries.size + 12 + s.idatData.size by omega] at h
  rw [h]
  have hChunkSize :
      (mkChunkBytes idatTypeBytes s.idatData).size =
        12 + s.idatData.size := by
    rw [mkChunkBytes_size _ _ (by rfl : idatTypeBytes.size = 4)]
    omega
  rw [byteArray_extract_append_prefix
    (a := mkChunkBytes idatTypeBytes s.idatData)
    (b := mkChunkBytes iendTypeBytes ByteArray.empty)
    (n := 12 + s.idatData.size)
    (by rw [hChunkSize])]
  rw [← hChunkSize]
  exact ByteArray.extract_zero_size

/-- The IEND chunk bytes live after the IDAT chunk.
This is the wrapped-chunk fact used by `readChunk_iend`. -/
lemma bytes_extract_iend (s : PaletteContainerSpec) :
    s.bytes.extract (57 + s.palette.entries.size + s.idatData.size)
        (57 + s.palette.entries.size + s.idatData.size + 12 + ByteArray.empty.size) =
      mkChunkBytes iendTypeBytes ByteArray.empty := by
  have hSize :
      57 + s.palette.entries.size + s.idatData.size +
          (12 + ByteArray.empty.size) ≤ s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s]
    simp
    omega
  have h := bytes_extract_skip_through_idat s 0
    (12 + ByteArray.empty.size) hSize
  simp only [Nat.add_zero] at h
  rw [show (57 + s.palette.entries.size + s.idatData.size +
        (12 + ByteArray.empty.size) : Nat) =
      57 + s.palette.entries.size + s.idatData.size + 12 + ByteArray.empty.size
      by omega] at h
  rw [h]
  have hChunkSize :
      (mkChunkBytes iendTypeBytes ByteArray.empty).size =
        12 + ByteArray.empty.size := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]
    simp
  rw [show (12 + ByteArray.empty.size : Nat) =
      (mkChunkBytes iendTypeBytes ByteArray.empty).size from hChunkSize.symm]
  exact ByteArray.extract_zero_size

/-- The length field of a `mkChunkBytes` wrapper is the payload size.
This is the first field read by the generic palette chunk parser lemma. -/
private lemma mkChunkBytes_extract_len (typBytes data : ByteArray) :
    (mkChunkBytes typBytes data).extract 0 4 = u32be data.size := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  simpa [mkChunkBytes_def, hlen] using
    (ByteArray.extract_append_eq_left
      (a := u32be data.size)
      (b := typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat)
      (i := (u32be data.size).size) rfl)

/-- The type field of a `mkChunkBytes` wrapper is stored at bytes 4 through 7.
This feeds the generic `readChunk` reduction for scaffold chunks. -/
private lemma mkChunkBytes_extract_type (typBytes data : ByteArray)
    (htyp : typBytes.size = 4) :
    (mkChunkBytes typBytes data).extract 4 8 = typBytes := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have h1 :
      (mkChunkBytes typBytes data).extract 4 8 =
        (typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 4 := by
    simpa [mkChunkBytes_def, hlen, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size)
        (b := typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat)
        (i := 0) (j := 4))
  have h2' :
      (typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract 0
          typBytes.size = typBytes := by
    simpa [ByteArray.append_assoc] using
      (ByteArray.extract_append_eq_left
        (a := typBytes)
        (b := data ++ u32be (crc32Chunk typBytes data).toNat)
        (i := typBytes.size) rfl)
  have h2 :
      (typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 4 =
        typBytes := by
    simpa [htyp] using h2'
  rw [h1, h2]

/-- The payload field of a `mkChunkBytes` wrapper starts after length and type.
This connects a wrapped chunk back to its original payload bytes. -/
private lemma mkChunkBytes_extract_data (typBytes data : ByteArray)
    (htyp : typBytes.size = 4) :
    (mkChunkBytes typBytes data).extract 8 (8 + data.size) = data := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have hprefix : (u32be data.size ++ typBytes).size = 8 := by
    rw [ByteArray.size_append, hlen, htyp]
  have h1 :
      (mkChunkBytes typBytes data).extract 8 (8 + data.size) =
        (data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 data.size := by
    simpa [mkChunkBytes_def, hprefix, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size ++ typBytes)
        (b := data ++ u32be (crc32Chunk typBytes data).toNat)
        (i := 0) (j := data.size))
  have h2 :
      (data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 data.size = data := by
    simpa using
      (ByteArray.extract_append_eq_left
        (a := data)
        (b := u32be (crc32Chunk typBytes data).toNat)
        (i := data.size) rfl)
  rw [h1, h2]

/-- The CRC trailer of a `mkChunkBytes` wrapper follows the payload.
This supplies the equality checked by `readChunk`. -/
private lemma mkChunkBytes_extract_crc (typBytes data : ByteArray)
    (htyp : typBytes.size = 4) :
    (mkChunkBytes typBytes data).extract (8 + data.size) (12 + data.size) =
      u32be (crc32Chunk typBytes data).toNat := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have hprefix : (u32be data.size ++ typBytes ++ data).size = 8 + data.size := by
    rw [ByteArray.size_append, ByteArray.size_append, hlen, htyp]
  rw [mkChunkBytes_def]
  have h1 :
      (u32be data.size ++ typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract
          (8 + data.size) (12 + data.size) =
        (u32be (crc32Chunk typBytes data).toNat).extract 0 4 := by
    have h := ByteArray.extract_append_size_add
      (a := u32be data.size ++ typBytes ++ data)
      (b := u32be (crc32Chunk typBytes data).toNat)
      (i := 0) (j := 4)
    rw [hprefix] at h
    rw [show (12 + data.size : Nat) = 8 + data.size + 4 by omega]
    simpa using h
  rw [h1]
  have hcrcLen : (u32be (crc32Chunk typBytes data).toNat).size = 4 := u32be_size _
  rw [show (4 : Nat) = (u32be (crc32Chunk typBytes data).toNat).size from hcrcLen.symm]
  exact ByteArray.extract_zero_size

set_option maxHeartbeats 800000 in
/-- Generic `readChunk` reduction for a wrapped chunk inside a byte stream.
The palette scaffold uses this for IHDR, PLTE, IDAT, and IEND. -/
lemma readChunk_at_mkChunkBytes (bytes : ByteArray) (pos : Nat)
    (typBytes data : ByteArray)
    (hTypSize : typBytes.size = 4)
    (hDataSize : data.size < 2 ^ 32)
    (hWrap : bytes.extract pos (pos + 12 + data.size) = mkChunkBytes typBytes data)
    (hSize : pos + 12 + data.size ≤ bytes.size)
    (hLen : pos + 3 < bytes.size) :
    readChunk bytes pos hLen =
      some (typBytes, data, pos + 8 + data.size + 4) := by
  have hSubExtract : ∀ (a b : Nat), a ≤ b → b ≤ 12 + data.size →
      bytes.extract (pos + a) (pos + b) =
        (mkChunkBytes typBytes data).extract a b := by
    intro a b _hab hb
    have hMin : min (pos + b) (pos + 12 + data.size) = pos + b := by
      omega
    have hExt :
        (bytes.extract pos (pos + 12 + data.size)).extract a b =
          bytes.extract (pos + a) (pos + b) := by
      have h := ByteArray.extract_extract (a := bytes)
        (i := pos) (j := pos + 12 + data.size) (k := a) (l := b)
      rw [hMin] at h
      exact h
    rw [← hExt, hWrap]
  have hExtractLen :
      bytes.extract pos (pos + 4) = u32be data.size := by
    have h := hSubExtract 0 4 (by omega) (by omega)
    simp at h
    rw [h]
    exact mkChunkBytes_extract_len typBytes data
  have hLenRead : readU32BE bytes pos hLen = data.size :=
    readU32BE_of_extract_eq bytes pos data.size hLen hExtractLen hDataSize
  have hExtractType :
      bytes.extract (pos + 4) (pos + 8) = typBytes := by
    have h := hSubExtract 4 8 (by omega) (by omega)
    rw [h]
    exact mkChunkBytes_extract_type typBytes data hTypSize
  have hExtractData :
      bytes.extract (pos + 8) (pos + 8 + data.size) = data := by
    have h := hSubExtract 8 (8 + data.size) (by omega) (by omega)
    rw [show pos + 8 + data.size = pos + (8 + data.size) by omega]
    rw [h]
    exact mkChunkBytes_extract_data typBytes data hTypSize
  have hExtractCrc :
      bytes.extract (pos + 8 + data.size) (pos + 12 + data.size) =
        u32be (crc32Chunk typBytes data).toNat := by
    have h := hSubExtract (8 + data.size) (12 + data.size) (by omega) (by omega)
    rw [show pos + 8 + data.size = pos + (8 + data.size) by omega,
        show pos + 12 + data.size = pos + (12 + data.size) by omega]
    rw [h]
    exact mkChunkBytes_extract_crc typBytes data hTypSize
  have hExtractCrc' :
      bytes.extract (pos + 8 + data.size) (pos + 8 + data.size + 4) =
        u32be (crc32Chunk typBytes data).toNat := by
    rw [show pos + 8 + data.size + 4 = pos + 12 + data.size by omega]
    exact hExtractCrc
  have hCrcRead :
      readU32BE bytes (pos + 8 + data.size) (by omega) =
        (crc32Chunk typBytes data).toNat :=
    readU32BE_of_extract_eq bytes (pos + 8 + data.size) _
      (by omega) hExtractCrc' (UInt32.toNat_lt _)
  have hCrcEnd : pos + 8 + data.size + 4 ≤ bytes.size := by omega
  unfold readChunk
  simp [hLenRead, hCrcEnd, hExtractType, hExtractData, hCrcRead]

/-- `readChunk` at byte 8 reads the IHDR chunk from the palette scaffold.
This is the first chunk-read fact for the full parser proof. -/
lemma readChunk_ihdr (s : PaletteContainerSpec)
    (hLen : 8 + 3 < s.bytes.size) :
    readChunk s.bytes 8 hLen =
      some (ihdrTypeBytes, encodeIHDRData s.header, 33) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hSize : 8 + 12 + (encodeIHDRData s.header).size ≤ s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s, hIhdrSize]
    omega
  have hFits : (encodeIHDRData s.header).size < 2 ^ 32 := by
    rw [hIhdrSize]
    decide
  have h := readChunk_at_mkChunkBytes s.bytes 8 ihdrTypeBytes
    (encodeIHDRData s.header) (by rfl) hFits (bytes_extract_ihdr s) hSize hLen
  rw [show 8 + 8 + (encodeIHDRData s.header).size + 4 = 33 by rw [hIhdrSize]] at h
  exact h

/-- `readChunk` at byte 33 reads the required PLTE chunk.
This proves the palette payload appears before IDAT at the expected offset. -/
lemma readChunk_plte (s : PaletteContainerSpec)
    (hPaletteSize : s.palette.entries.size < 2 ^ 32)
    (hLen : 33 + 3 < s.bytes.size) :
    readChunk s.bytes 33 hLen =
      some (plteTypeBytes, s.palette.entries, 45 + s.palette.entries.size) := by
  have hSize : 33 + 12 + s.palette.entries.size ≤ s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s]
    omega
  have h := readChunk_at_mkChunkBytes s.bytes 33 plteTypeBytes
    s.palette.entries (by rfl) hPaletteSize (bytes_extract_plte s) hSize hLen
  rw [show 33 + 8 + s.palette.entries.size + 4 =
      45 + s.palette.entries.size by omega] at h
  exact h

/-- `readChunk` after PLTE reads the single IDAT chunk.
This is the payload-position fact for the indexed image data. -/
lemma readChunk_idat (s : PaletteContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32)
    (hLen : (45 + s.palette.entries.size) + 3 < s.bytes.size) :
    readChunk s.bytes (45 + s.palette.entries.size) hLen =
      some (idatTypeBytes, s.idatData,
        57 + s.palette.entries.size + s.idatData.size) := by
  have hSize :
      45 + s.palette.entries.size + 12 + s.idatData.size ≤ s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s]
    omega
  have h := readChunk_at_mkChunkBytes s.bytes
    (45 + s.palette.entries.size) idatTypeBytes s.idatData
    (by rfl) hIdatSize (bytes_extract_idat s) hSize hLen
  rw [show 45 + s.palette.entries.size + 8 + s.idatData.size + 4 =
      57 + s.palette.entries.size + s.idatData.size by omega] at h
  exact h

/-- `readChunk` after IDAT reads the final empty IEND chunk.
This closes the concrete chunk sequence of the palette scaffold. -/
lemma readChunk_iend (s : PaletteContainerSpec)
    (hLen : (57 + s.palette.entries.size + s.idatData.size) + 3 < s.bytes.size) :
    readChunk s.bytes (57 + s.palette.entries.size + s.idatData.size) hLen =
      some (iendTypeBytes, ByteArray.empty, s.bytes.size) := by
  have hSize :
      57 + s.palette.entries.size + s.idatData.size + 12 + ByteArray.empty.size ≤
        s.bytes.size := by
    rw [PaletteContainerSpec.bytes_size s]
    simp
    omega
  have hFits : (ByteArray.empty : ByteArray).size < 2 ^ 32 := by decide
  have h := readChunk_at_mkChunkBytes s.bytes
    (57 + s.palette.entries.size + s.idatData.size) iendTypeBytes ByteArray.empty
    (by rfl) hFits (bytes_extract_iend s) hSize hLen
  rw [show 57 + s.palette.entries.size + s.idatData.size + 8 +
        ByteArray.empty.size + 4 = s.bytes.size by
      rw [PaletteContainerSpec.bytes_size s]
      simp
      omega] at h
  exact h

/-- Metadata returned by the minimal palette scaffold parser walk.
It records exactly the required PLTE payload and no ancillary metadata. -/
def metadata (s : PaletteContainerSpec) : PngMetadata :=
  { PngMetadata.empty with palette := some s.palette }

/-- Parsed result returned by the minimal palette scaffold parser walk.
This packages the scaffold header, IDAT payload, and palette metadata. -/
def parsed (s : PaletteContainerSpec) : PngParsed :=
  { header := s.header, idat := s.idatData, metadata := metadata s }

/-- Reading the IHDR length field in the palette scaffold yields 13.
This supplies the header-length branch condition for the parser loop. -/
lemma readU32BE_ihdr_len (s : PaletteContainerSpec)
    (hLen : 8 + 3 < s.bytes.size) :
    readU32BE s.bytes 8 hLen = 13 := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hExtractLen : s.bytes.extract 8 (8 + 4) = u32be 13 := by
    have h := bytes_extract_ihdr s
    have hChunkLen := mkChunkBytes_extract_len ihdrTypeBytes (encodeIHDRData s.header)
    rw [hIhdrSize] at hChunkLen
    have hsub :
        (s.bytes.extract 8 (8 + 12 + (encodeIHDRData s.header).size)).extract 0 4 =
          (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).extract 0 4 := by
      rw [h]
    rw [hChunkLen] at hsub
    have hExt := ByteArray.extract_extract (a := s.bytes) (i := 8)
      (j := 8 + 12 + (encodeIHDRData s.header).size) (k := 0) (l := 4)
    have hMin : min (8 + 4) (8 + 12 + (encodeIHDRData s.header).size) = 8 + 4 := by
      rw [hIhdrSize]
      omega
    rw [hMin] at hExt
    rw [← hExt]
    exact hsub
  exact readU32BE_of_extract_eq s.bytes 8 13 hLen hExtractLen (by decide)

/-- Metadata-aware IEND success for the palette scaffold.
This local branch lemma closes the four-chunk parser-loop walk. -/
lemma parsePngLoopFuelWithMetadata_iend_success_step (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen =
      some (iendTypeBytes, ByteArray.empty, bytes.size))
    (hheader : state.header = some hdr)
    (hSeenIDAT : state.seenIDAT = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      some { header := hdr, idat := state.idat, metadata := state.metadata } := by
  conv => lhs; unfold parsePngLoopFuelWithMetadata
  have hNotIHDR : (iendTypeBytes == ihdrTypeBytes) = false := by decide
  have hNotPLTE : (iendTypeBytes == plteTypeBytes) = false := by decide
  have hNotIDAT : (iendTypeBytes == idatTypeBytes) = false := by decide
  have hIsIEND : (iendTypeBytes == iendTypeBytes) = true := by decide
  simp [hpos, hLen, hread, hheader, hNotIHDR, hNotPLTE, hNotIDAT, hIsIEND,
    hSeenIDAT]

set_option maxHeartbeats 1200000 in
/-- The metadata-aware parser loop accepts the minimal indexed-palette stream
with any extra fuel. This is the loop form needed by parser wrappers that use
`bytes.size + 1` fuel. -/
theorem parsePngLoopFuelWithMetadata_accepts_with_extra (s : PaletteContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32) (extra : Nat) :
    parsePngLoopFuelWithMetadata (extra + 4) s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some (parsed s) := by
  have hSizeEq : s.bytes.size = s.idatData.size + s.palette.entries.size + 69 :=
    PaletteContainerSpec.bytes_size s
  have hPaletteSize : s.palette.entries.size < 2 ^ 32 := by
    have h := s.hPaletteMax
    omega
  have hBDlt : s.header.bitDepth < 256 := by
    rcases s.hBitDepth with h | h | h | h <;> rw [h] <;> decide
  have hCTlt : s.header.colorType < 256 := by
    rw [s.hColorType]
    decide
  have hParseHdr :=
    parseIHDRData_encodeIHDRData_lt256 s.header
      s.hWidth s.hHeight hBDlt s.hInterlace hCTlt
  have hLenIhdr : (8 : Nat) + 3 < s.bytes.size := by rw [hSizeEq]; omega
  have hPosIhdr : (8 : Nat) + 8 ≤ s.bytes.size := by rw [hSizeEq]; omega
  have hReadIhdr := readChunk_ihdr s hLenIhdr
  have hReadLen := readU32BE_ihdr_len s hLenIhdr
  conv => lhs; unfold parsePngLoopFuelWithMetadata
  simp [hPosIhdr, hLenIhdr, hReadIhdr, hReadLen, hParseHdr]
  refine ⟨by decide, ?_⟩

  let stateAfterIhdr : PngMetadataParseState :=
    { header := some s.header, idat := ByteArray.empty,
      seenPLTE := false, seenIDAT := false, closedIDAT := false,
      metadata := PngMetadata.empty }
  let stateAfterPlte : PngMetadataParseState :=
    { header := some s.header, idat := ByteArray.empty,
      seenPLTE := true, seenIDAT := false, closedIDAT := false,
      metadata := metadata s }
  let stateAfterIdat : PngMetadataParseState :=
    { header := some s.header, idat := s.idatData,
      seenPLTE := true, seenIDAT := true, closedIDAT := false,
      metadata := metadata s }

  have hChangeIhdr :
      parsePngLoopFuelWithMetadata (extra + 3) s.bytes 33
        { header := some s.header, idat := ByteArray.empty,
          seenPLTE := false, seenIDAT := false, closedIDAT := false,
          metadata := PngMetadata.empty } =
      parsePngLoopFuelWithMetadata (extra + 3) s.bytes 33 stateAfterIhdr := by
    rfl
  rw [hChangeIhdr]

  have hLenPlte : (33 : Nat) + 3 < s.bytes.size := by rw [hSizeEq]; omega
  have hPosPlte : (33 : Nat) + 8 ≤ s.bytes.size := by rw [hSizeEq]; omega
  have hReadPlte := readChunk_plte s hPaletteSize hLenPlte
  have hNotIhdrPlte : (plteTypeBytes == ihdrTypeBytes) = false := by decide
  have hIsPlte : (plteTypeBytes == plteTypeBytes) = true := by decide
  have hSeenPlte : (stateAfterIhdr.seenPLTE || stateAfterIhdr.seenIDAT) = false := by
    rfl
  have hMetadataPlte :
      (stateAfterIhdr.metadata.transparency.isSome ||
        stateAfterIhdr.metadata.background.isSome) = false := by
    rfl
  have hAllowed : plteAllowedForColorType s.header.colorType = true := by
    rw [s.hColorType]
    decide
  have hStepPlte :=
    parsePngLoopFuelWithMetadata_accepts_PLTE (extra + 2) s.bytes 33 stateAfterIhdr
      s.header plteTypeBytes s.palette.entries (45 + s.palette.entries.size)
      s.palette hPosPlte hLenPlte hReadPlte rfl hNotIhdrPlte hIsPlte
      hSeenPlte hMetadataPlte hAllowed (parsePlteData s)
  rw [show (extra + 3 : Nat) = (extra + 2) + 1 by omega]
  rw [hStepPlte]
  change parsePngLoopFuelWithMetadata (extra + 2) s.bytes (45 + s.palette.entries.size)
      stateAfterPlte =
    some (parsed s)

  have hLenIdat :
      (45 + s.palette.entries.size : Nat) + 3 < s.bytes.size := by
    rw [hSizeEq]
    omega
  have hPosIdat :
      (45 + s.palette.entries.size : Nat) + 8 ≤ s.bytes.size := by
    rw [hSizeEq]
    omega
  have hReadIdat := readChunk_idat s hIdatSize hLenIdat
  have hNotIhdrIdat : (idatTypeBytes == ihdrTypeBytes) = false := by decide
  have hNotPlteIdat : (idatTypeBytes == plteTypeBytes) = false := by decide
  have hIsIdat : (idatTypeBytes == idatTypeBytes) = true := by decide
  have hPaletteIdat : (s.header.colorType == 3 && !stateAfterPlte.seenPLTE) = false := by
    simp [stateAfterPlte]
  have hStepIdat :=
    parsePngLoopFuelWithMetadata_idat_appends_when_open (extra + 1) s.bytes
      (45 + s.palette.entries.size) stateAfterPlte s.header idatTypeBytes
      s.idatData (57 + s.palette.entries.size + s.idatData.size)
      hPosIdat hLenIdat hReadIdat rfl hNotIhdrIdat hNotPlteIdat hIsIdat
      rfl hPaletteIdat
  rw [show (extra + 2 : Nat) = (extra + 1) + 1 by omega]
  rw [hStepIdat]
  change parsePngLoopFuelWithMetadata (extra + 1) s.bytes
      (57 + s.palette.entries.size + s.idatData.size) stateAfterIdat =
    some (parsed s)

  have hLenIend :
      (57 + s.palette.entries.size + s.idatData.size : Nat) + 3 < s.bytes.size := by
    rw [hSizeEq]
    omega
  have hPosIend :
      (57 + s.palette.entries.size + s.idatData.size : Nat) + 8 ≤ s.bytes.size := by
    rw [hSizeEq]
    omega
  have hReadIend := readChunk_iend s hLenIend
  have hStepIend :=
    parsePngLoopFuelWithMetadata_iend_success_step extra s.bytes
      (57 + s.palette.entries.size + s.idatData.size) stateAfterIdat
      s.header hPosIend hLenIend hReadIend rfl rfl
  rw [hStepIend]
  simp [stateAfterIdat, parsed]

/-- The exact four-fuel parser-loop theorem for the minimal indexed-palette
stream. This is the no-extra-fuel specialization of the generalized walk. -/
theorem parsePngLoopFuelWithMetadata_accepts (s : PaletteContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32) :
    parsePngLoopFuelWithMetadata 4 s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some (parsed s) := by
  simpa using parsePngLoopFuelWithMetadata_accepts_with_extra s hIdatSize 0

/-- The simple PNG fast path rejects the indexed-palette scaffold.
The fast path only accepts non-palette color types, so color type 3 falls through
to the general parser loop. -/
lemma parsePngSimple_eq_none (s : PaletteContainerSpec) :
    parsePngSimple s.bytes s.bytes_size_ge_8 = none := by
  unfold parsePngSimple
  have hSizeEq : s.bytes.size = s.idatData.size + s.palette.entries.size + 69 :=
    PaletteContainerSpec.bytes_size s
  have hSig : s.bytes.extract 0 8 = pngSignature := bytes_extract_signature s
  have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
    rw [hSig]
    exact bne_self_eq_false' (a := pngSignature)
  have hLenIhdr : (8 : Nat) + 3 < s.bytes.size := by rw [hSizeEq]; omega
  have hReadIhdr := readChunk_ihdr s hLenIhdr
  have hBDlt : s.header.bitDepth < 256 := by
    rcases s.hBitDepth with h | h | h | h <;> rw [h] <;> decide
  have hCTlt : s.header.colorType < 256 := by
    rw [s.hColorType]
    decide
  have hParseHdr :=
    parseIHDRData_encodeIHDRData_lt256 s.header
      s.hWidth s.hHeight hBDlt s.hInterlace hCTlt
  have hSupported :
      pngColorTypeBitDepthSupported s.header.colorType s.header.bitDepth = true :=
    s.hCtBdSupported
  simp [hSigCheck, hLenIhdr, hReadIhdr, hParseHdr, hSupported]
  intro _ hColor
  have hNot0 : ¬s.header.colorType = 0 := by rw [s.hColorType]; decide
  have hNot2 : ¬s.header.colorType = 2 := by rw [s.hColorType]; decide
  have hNot4 : ¬s.header.colorType = 4 := by rw [s.hColorType]; decide
  have h6 := hColor hNot0 hNot2 hNot4
  rw [s.hColorType] at h6
  exact False.elim ((by decide : (3 : Nat) ≠ 6) h6)

/-- The metadata-aware simple fast path also rejects the palette scaffold.
It delegates to `parsePngSimple`, so this follows from the fast-path rejection. -/
lemma parsePngSimpleWithMetadata_eq_none (s : PaletteContainerSpec) :
    parsePngSimpleWithMetadata s.bytes s.bytes_size_ge_8 = none := by
  unfold parsePngSimpleWithMetadata
  simp [parsePngSimple_eq_none s]

/-- `parsePngWithMetadata` accepts the indexed-palette scaffold.
After the simple fast path rejects color type 3, the general parser loop records
the PLTE metadata and returns the scaffold payload. -/
theorem parsePngWithMetadata_accepts (s : PaletteContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32) :
    parsePngWithMetadata s.bytes s.bytes_size_ge_8 = some (parsed s) := by
  unfold parsePngWithMetadata
  have hSizeEq : s.bytes.size = s.idatData.size + s.palette.entries.size + 69 :=
    PaletteContainerSpec.bytes_size s
  have hSimple : parsePngSimpleWithMetadata s.bytes s.bytes_size_ge_8 = none :=
    parsePngSimpleWithMetadata_eq_none s
  have hSig : s.bytes.extract 0 8 = pngSignature := bytes_extract_signature s
  have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
    rw [hSig]
    exact bne_self_eq_false' (a := pngSignature)
  have hFuel :
      s.bytes.size + 1 = (s.bytes.size - 3) + 4 := by
    rw [hSizeEq]
    omega
  simp [hSimple, hSigCheck]
  rw [hFuel]
  exact parsePngLoopFuelWithMetadata_accepts_with_extra s hIdatSize (s.bytes.size - 3)

/-- `parsePngForDecode` accepts the indexed-palette scaffold.
This is the parser wrapper used by the public indexed decode entrypoints. -/
theorem parsePngForDecode_accepts (s : PaletteContainerSpec)
    (hIdatSize : s.idatData.size < 2 ^ 32) :
    parsePngForDecode s.bytes s.bytes_size_ge_8 = some (parsed s) := by
  unfold parsePngForDecode
  simp [parsePngSimpleWithMetadata_eq_none s, parsePngWithMetadata_accepts s hIdatSize]

end PaletteContainerSpec

end Lemmas

end Bitmaps
