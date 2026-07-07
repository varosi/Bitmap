import Bitmap.Lemmas.Png.PaletteContainerRoundTrip

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette public encoder round-trip layer

These theorems connect the public checked indexed encoder API to the palette
container decoder proofs.  The current proof scope is explicit 8-bit indexed
input with a full 256-entry palette, filter-0 rows, and no optional palette
alpha or background chunks. -/

namespace PaletteEncoderRoundTrip

private def options (mode : PngEncodeMode) : PngEncodeOptions :=
  { mode := mode, filter := .none }

/-- A full 256-entry byte palette has exactly 256 entries.
This converts the public encoder's byte-size invariant into decoder shape. -/
lemma entryCount_of_entries_size_256 (palette : PngPalette)
    (hsize : palette.entries.size = 256 * 3) :
    palette.entryCount = 256 := by
  simp [PngPalette.entryCount, hsize]

/-- The checked indexed encoder accepts the concrete 8-bit full-palette shape
used by the top-level round-trip theorems. -/
lemma validateIndexedBitmap_accepts_8_256 (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    validateIndexedBitmap bmp = Except.ok () := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := by
    exact Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := by
    exact Nat.not_le_of_gt hh
  have hpalCount : bmp.palette.entryCount = 256 :=
    entryCount_of_entries_size_256 bmp.palette hpalSize
  have hrange256 : indexedDataInRange bmp.data 256 = true := by
    simpa [hpalCount] using hrange
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hpalSize, hpalCount, hrange256, htrans, hbg,
    paletteMaxEntriesForBitDepth]
  rfl

private def encodedSpec (bmp : PngIndexedBitmap) (idat : ByteArray)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hpalSize : bmp.palette.entries.size = 256 * 3) : PaletteContainerSpec :=
  { header :=
      { width := bmp.size.width, height := bmp.size.height, colorType := 3,
        bitDepth := 8, interlace := 0 }
    palette := bmp.palette
    idatData := idat
    hBitDepth := by
      right
      right
      right
      rfl
    hColorType := by
      rfl
    hCtBdSupported := by
      rfl
    hInterlace := by
      left
      rfl
    hWidth := by
      simpa [UInt32.size] using hw
    hHeight := by
      simpa [UInt32.size] using hh
    hPaletteNonempty := by
      simp [hpalSize]
    hPaletteTriplets := by
      simp [hpalSize]
    hPaletteMax := by
      simp [hpalSize]
    hPaletteFits := by
      simp [PngPalette.entryCount, hpalSize, paletteMaxEntriesForBitDepth] }

private lemma encodeIndexedBitmapWithOptionsChecked_stored_eq_spec_bytes
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    let s := encodedSpec bmp
      (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)) hw hh hpalSize
    encodeIndexedBitmapWithOptionsChecked bmp (options .stored) = Except.ok s.bytes := by
  intro s
  have hvalid :=
    validateIndexedBitmap_accepts_8_256 bmp hw hh hbd hpalSize hrange htrans hbg
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  unfold encodeIndexedBitmapWithOptions options PaletteContainerSpec.bytes encodeIHDRData
  simp [hbd, htrans, hbg, s, encodedSpec, encodeColorSpaceChunks?,
    encodeChrmChunk?, encodePhysChunk?, encodeTimeChunk?, ByteArray.append_assoc]
  rfl

private lemma encodeIndexedBitmapWithOptionsChecked_fixed_eq_spec_bytes
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    let s := encodedSpec bmp
      (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)) hw hh hpalSize
    encodeIndexedBitmapWithOptionsChecked bmp (options .fixed) = Except.ok s.bytes := by
  intro s
  have hvalid :=
    validateIndexedBitmap_accepts_8_256 bmp hw hh hbd hpalSize hrange htrans hbg
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  unfold encodeIndexedBitmapWithOptions options PaletteContainerSpec.bytes encodeIHDRData
  simp [hbd, htrans, hbg, s, encodedSpec, encodeColorSpaceChunks?,
    encodeChrmChunk?, encodePhysChunk?, encodeTimeChunk?, ByteArray.append_assoc]
  rfl

private lemma encodeIndexedBitmapWithOptionsChecked_dynamic_eq_spec_bytes
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    let s := encodedSpec bmp
      (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)) hw hh hpalSize
    encodeIndexedBitmapWithOptionsChecked bmp (options .dynamic) = Except.ok s.bytes := by
  intro s
  have hvalid :=
    validateIndexedBitmap_accepts_8_256 bmp hw hh hbd hpalSize hrange htrans hbg
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  unfold encodeIndexedBitmapWithOptions options PaletteContainerSpec.bytes encodeIHDRData
  simp [hbd, htrans, hbg, s, encodedSpec, encodeColorSpaceChunks?,
    encodeChrmChunk?, encodePhysChunk?, encodeTimeChunk?, ByteArray.append_assoc]
  rfl

/-- Stored-zlib checked indexed encode succeeds, and both indexed decode APIs
recover the original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_stored_8_256_data
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (hIdatSize :
      (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)).size < 2 ^ 32) :
    ∃ bytes,
      encodeIndexedBitmapChecked bmp .stored = Except.ok bytes ∧
        (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data) =
          some bmp.data ∧
        (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  let s := encodedSpec bmp
    (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)) hw hh hpalSize
  have hEncode :
      encodeIndexedBitmapChecked bmp .stored = Except.ok s.bytes := by
    unfold encodeIndexedBitmapChecked
    simpa [options] using
      encodeIndexedBitmapWithOptionsChecked_stored_eq_spec_bytes
        bmp hw hh hbd hpalSize hrange htrans hbg
  have hpal : bmp.palette.entryCount = 256 :=
    entryCount_of_entries_size_256 bmp.palette hpalSize
  have hMetadata :=
    PaletteContainerSpec.decodeIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_256_data
      s bmp rfl rfl rfl hIdatSize hbd hpal
  have hPixel :=
    PaletteContainerSpec.decodeIndexedBitmap_stored_encodeRawIndexed_none_8_256_data
      s bmp rfl rfl rfl hIdatSize hbd hpal
  exact ⟨s.bytes, hEncode, hMetadata, hPixel⟩

/-- Fixed-Huffman checked indexed encode succeeds, and both indexed decode APIs
recover the original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_fixed_8_256_data
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (hIdatSize :
      (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)).size < 2 ^ 32) :
    ∃ bytes,
      encodeIndexedBitmapChecked bmp .fixed = Except.ok bytes ∧
        (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data) =
          some bmp.data ∧
        (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  let s := encodedSpec bmp
    (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)) hw hh hpalSize
  have hEncode :
      encodeIndexedBitmapChecked bmp .fixed = Except.ok s.bytes := by
    unfold encodeIndexedBitmapChecked
    simpa [options] using
      encodeIndexedBitmapWithOptionsChecked_fixed_eq_spec_bytes
        bmp hw hh hbd hpalSize hrange htrans hbg
  have hpal : bmp.palette.entryCount = 256 :=
    entryCount_of_entries_size_256 bmp.palette hpalSize
  have hMetadata :=
    PaletteContainerSpec.decodeIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_256_data
      s bmp rfl rfl rfl hIdatSize hbd hpal
  have hPixel :=
    PaletteContainerSpec.decodeIndexedBitmap_fixed_encodeRawIndexed_none_8_256_data
      s bmp rfl rfl rfl hIdatSize hbd hpal
  exact ⟨s.bytes, hEncode, hMetadata, hPixel⟩

/-- Dynamic-Huffman checked indexed encode succeeds, and both indexed decode APIs
recover the original index bytes for 8-bit full-palette filter-0 inputs. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_dynamic_8_256_data
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (hIdatSize :
      (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size < 2 ^ 32) :
    ∃ bytes,
      encodeIndexedBitmapChecked bmp .dynamic = Except.ok bytes ∧
        (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data) =
          some bmp.data ∧
        (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  let s := encodedSpec bmp
    (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)) hw hh hpalSize
  have hEncode :
      encodeIndexedBitmapChecked bmp .dynamic = Except.ok s.bytes := by
    unfold encodeIndexedBitmapChecked
    simpa [options] using
      encodeIndexedBitmapWithOptionsChecked_dynamic_eq_spec_bytes
        bmp hw hh hbd hpalSize hrange htrans hbg
  have hpal : bmp.palette.entryCount = 256 :=
    entryCount_of_entries_size_256 bmp.palette hpalSize
  have hMetadata :=
    PaletteContainerSpec.decodeIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_256_data
      s bmp rfl rfl rfl hIdatSize hbd hpal
  have hPixel :=
    PaletteContainerSpec.decodeIndexedBitmap_dynamic_encodeRawIndexed_none_8_256_data
      s bmp rfl rfl rfl hIdatSize hbd hpal
  exact ⟨s.bytes, hEncode, hMetadata, hPixel⟩

/-- Checked indexed encode/decode round-trips 8-bit full-palette filter-0
inputs for every supported compression mode. This packages the per-mode
container proofs behind the public `encodeIndexedBitmapChecked` API. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_8_256_data
    (mode : PngEncodeMode)
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = 256 * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (hIdatSize :
      (match mode with
       | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
       | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
       | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size
        < 2 ^ 32) :
    ∃ bytes,
      encodeIndexedBitmapChecked bmp mode = Except.ok bytes ∧
        (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data) =
          some bmp.data ∧
        (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  cases mode
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_stored_8_256_data
      bmp hw hh hbd hpalSize hrange htrans hbg hIdatSize
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_fixed_8_256_data
      bmp hw hh hbd hpalSize hrange htrans hbg hIdatSize
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_dynamic_8_256_data
      bmp hw hh hbd hpalSize hrange htrans hbg hIdatSize

end PaletteEncoderRoundTrip

end Lemmas

end Bitmaps
