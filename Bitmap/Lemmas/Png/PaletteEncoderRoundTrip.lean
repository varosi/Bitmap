import Bitmap.Lemmas.Png.PaletteContainerRoundTrip
import Bitmap.Lemmas.Png.PaletteValidation

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette public encoder round-trip layer

These theorems connect the public checked indexed encoder API to the palette
container decoder proofs.  The generalized proof scope is explicit indexed
input at supported palette bit depths, filter-0 rows, no optional palette alpha
or background chunks, and source indices bounded by the actual palette size. -/

namespace PaletteEncoderRoundTrip

private def options (mode : PngEncodeMode) : PngEncodeOptions :=
  { mode := mode, filter := .none }

/-- A full 256-entry byte palette has exactly 256 entries.
This converts the public encoder's byte-size invariant into decoder shape. -/
lemma entryCount_of_entries_size_256 (palette : PngPalette)
    (hsize : palette.entries.size = 256 * 3) :
    palette.entryCount = 256 := by
  simp [PngPalette.entryCount, hsize]

/-- A byte palette sized to the selected packed-index limit has exactly that
many entries. This is the non-8-bit analogue of the 256-entry helper. -/
lemma entryCount_of_entries_size_paletteIndexLimit (palette : PngPalette) (bitDepth : Nat)
    (hsize : palette.entries.size = paletteIndexLimit bitDepth * 3) :
    palette.entryCount = paletteIndexLimit bitDepth := by
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

private lemma validateIndexedBitmap_accepts_non8_full
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    validateIndexedBitmap bmp = Except.ok () := by
  have hbdSupported :
      bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8 := by
    rcases hbd with hbd | hbd | hbd
    · exact Or.inl hbd
    · exact Or.inr (Or.inl hbd)
    · exact Or.inr (Or.inr (Or.inl hbd))
  have hpalCount : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth :=
    entryCount_of_entries_size_paletteIndexLimit bmp.palette bmp.bitDepth hpalSize
  have hpalNonempty : bmp.palette.entries.size ≠ 0 := by
    rcases hbd with hbd | hbd | hbd <;> simp [hpalSize, hbd, paletteIndexLimit]
  have hpalTriplets : bmp.palette.entries.size % 3 = 0 := by
    simp [hpalSize]
  have hpalMax : bmp.palette.entries.size ≤ 256 * 3 := by
    rcases hbd with hbd | hbd | hbd <;> simp [hpalSize, hbd, paletteIndexLimit]
  have hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth := by
    simp [hpalCount]
  exact
    PaletteValidation.validateIndexedBitmap_accepts_of_paletteIndexLimit
      bmp hbdSupported hw hh hpalNonempty hpalTriplets hpalMax hpalFits hrange
      (by intro alpha halpha; simp [htrans] at halpha)
      (by intro idx hidx; simp [hbg] at hidx)

/-- The checked indexed encoder accepts any supported palette bit depth when the
palette shape is valid, the palette fits that depth, and all source indices are
below the actual palette entry count. -/
private lemma validateIndexedBitmap_accepts_paletteRange
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalNonempty : bmp.palette.entries.size ≠ 0)
    (hpalTriplets : bmp.palette.entries.size % 3 = 0)
    (hpalMax : bmp.palette.entries.size ≤ 256 * 3)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    validateIndexedBitmap bmp = Except.ok () := by
  exact
    PaletteValidation.validateIndexedBitmap_accepts_of_paletteIndexLimit
      bmp hbd hw hh hpalNonempty hpalTriplets hpalMax hpalFits hrange
      (by intro alpha halpha; simp [htrans] at halpha)
      (by intro idx hidx; simp [hbg] at hidx)

private lemma indexedDataInRange_non8_full_of_coordinates
    (bmp : PngIndexedBitmap)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth) :
    indexedDataInRange bmp.data bmp.palette.entryCount = true := by
  have hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth :=
    entryCount_of_entries_size_paletteIndexLimit bmp.palette bmp.bitDepth hpalSize
  have hchecked :=
    PaletteValidation.indexedDataInRange_true_of_valid_coordinates
      bmp (paletteIndexLimit bmp.bitDepth) hrange
  simpa [hpal] using hchecked

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

private def encodedSpecNon8 (bmp : PngIndexedBitmap) (idat : ByteArray)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3) :
    PaletteContainerSpec :=
  { header :=
      { width := bmp.size.width, height := bmp.size.height, colorType := 3,
        bitDepth := bmp.bitDepth, interlace := 0 }
    palette := bmp.palette
    idatData := idat
    hBitDepth := by
      rcases hbd with hbd | hbd | hbd
      · exact Or.inl hbd
      · exact Or.inr (Or.inl hbd)
      · exact Or.inr (Or.inr (Or.inl hbd))
    hColorType := by
      rfl
    hCtBdSupported := by
      rcases hbd with hbd | hbd | hbd <;> simp [hbd, pngColorTypeBitDepthSupported]
    hInterlace := by
      left
      rfl
    hWidth := by
      simpa [UInt32.size] using hw
    hHeight := by
      simpa [UInt32.size] using hh
    hPaletteNonempty := by
      rcases hbd with hbd | hbd | hbd <;> simp [hpalSize, hbd, paletteIndexLimit]
    hPaletteTriplets := by
      simp [hpalSize]
    hPaletteMax := by
      rcases hbd with hbd | hbd | hbd <;> simp [hpalSize, hbd, paletteIndexLimit]
    hPaletteFits := by
      have hpalCount : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth :=
        entryCount_of_entries_size_paletteIndexLimit bmp.palette bmp.bitDepth hpalSize
      simp [hpalCount, paletteMaxEntriesForBitDepth_eq_paletteIndexLimit] }

/-- Palette container scaffold for checked indexed encoder output with an
arbitrary valid palette that fits the selected indexed bit depth. -/
private def encodedSpecPaletteRange (bmp : PngIndexedBitmap) (idat : ByteArray)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalNonempty : bmp.palette.entries.size ≠ 0)
    (hpalTriplets : bmp.palette.entries.size % 3 = 0)
    (hpalMax : bmp.palette.entries.size ≤ 256 * 3)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth) :
    PaletteContainerSpec :=
  { header :=
      { width := bmp.size.width, height := bmp.size.height, colorType := 3,
        bitDepth := bmp.bitDepth, interlace := 0 }
    palette := bmp.palette
    idatData := idat
    hBitDepth := by
      exact hbd
    hColorType := by
      rfl
    hCtBdSupported := by
      rcases hbd with hbd | hbd | hbd | hbd <;> simp [hbd, pngColorTypeBitDepthSupported]
    hInterlace := by
      left
      rfl
    hWidth := by
      simpa [UInt32.size] using hw
    hHeight := by
      simpa [UInt32.size] using hh
    hPaletteNonempty := hpalNonempty
    hPaletteTriplets := hpalTriplets
    hPaletteMax := hpalMax
    hPaletteFits := by
      simpa [paletteMaxEntriesForBitDepth_eq_paletteIndexLimit] using hpalFits }

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

private lemma encodeIndexedBitmapWithOptionsChecked_stored_eq_spec_bytes_non8
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    let s := encodedSpecNon8 bmp
      (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)) hw hh hbd hpalSize
    encodeIndexedBitmapWithOptionsChecked bmp (options .stored) = Except.ok s.bytes := by
  intro s
  have hvalid :=
    validateIndexedBitmap_accepts_non8_full bmp hw hh hbd hpalSize hrange htrans hbg
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  unfold encodeIndexedBitmapWithOptions options PaletteContainerSpec.bytes encodeIHDRData
  simp [htrans, hbg, s, encodedSpecNon8, encodeColorSpaceChunks?,
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

private lemma encodeIndexedBitmapWithOptionsChecked_fixed_eq_spec_bytes_non8
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    let s := encodedSpecNon8 bmp
      (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)) hw hh hbd hpalSize
    encodeIndexedBitmapWithOptionsChecked bmp (options .fixed) = Except.ok s.bytes := by
  intro s
  have hvalid :=
    validateIndexedBitmap_accepts_non8_full bmp hw hh hbd hpalSize hrange htrans hbg
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  unfold encodeIndexedBitmapWithOptions options PaletteContainerSpec.bytes encodeIHDRData
  simp [htrans, hbg, s, encodedSpecNon8, encodeColorSpaceChunks?,
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

private lemma encodeIndexedBitmapWithOptionsChecked_dynamic_eq_spec_bytes_non8
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    let s := encodedSpecNon8 bmp
      (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)) hw hh hbd hpalSize
    encodeIndexedBitmapWithOptionsChecked bmp (options .dynamic) = Except.ok s.bytes := by
  intro s
  have hvalid :=
    validateIndexedBitmap_accepts_non8_full bmp hw hh hbd hpalSize hrange htrans hbg
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  unfold encodeIndexedBitmapWithOptions options PaletteContainerSpec.bytes encodeIHDRData
  simp [htrans, hbg, s, encodedSpecNon8, encodeColorSpaceChunks?,
    encodeChrmChunk?, encodePhysChunk?, encodeTimeChunk?, ByteArray.append_assoc]
  rfl

/-- The checked indexed encoder emits the generalized palette scaffold for
filter-0 output whenever validation accepts the explicit indexed bitmap. -/
private lemma encodeIndexedBitmapWithOptionsChecked_eq_spec_bytes_paletteRange
    (mode : PngEncodeMode)
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalNonempty : bmp.palette.entries.size ≠ 0)
    (hpalTriplets : bmp.palette.entries.size % 3 = 0)
    (hpalMax : bmp.palette.entries.size ≤ 256 * 3)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none) :
    encodeIndexedBitmapWithOptionsChecked bmp (options mode) =
      Except.ok
        (encodedSpecPaletteRange bmp
          (match mode with
           | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
           | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
           | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none))
          hw hh hbd hpalNonempty hpalTriplets hpalMax hpalFits).bytes := by
  have hvalid :=
    validateIndexedBitmap_accepts_paletteRange bmp hw hh hbd hpalNonempty
      hpalTriplets hpalMax hpalFits hrange htrans hbg
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  cases mode <;>
    unfold encodeIndexedBitmapWithOptions options PaletteContainerSpec.bytes encodeIHDRData <;>
    simp [htrans, hbg, encodedSpecPaletteRange, encodeColorSpaceChunks?,
      encodeChrmChunk?, encodePhysChunk?, encodeTimeChunk?, ByteArray.append_assoc] <;>
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

/-- Stored-zlib checked indexed encode succeeds, and both indexed decode APIs
recover the original index bytes for 1/2/4-bit full-addressable-palette
filter-0 inputs. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_stored_non8_data
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (hIdatSize :
      (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)).size < 2 ^ 32) :
    ∃ bytes,
      encodeIndexedBitmapChecked bmp .stored = Except.ok bytes ∧
        (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data) =
          some bmp.data ∧
        (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  let s := encodedSpecNon8 bmp
    (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)) hw hh hbd hpalSize
  have hEncode :
      encodeIndexedBitmapChecked bmp .stored = Except.ok s.bytes := by
    unfold encodeIndexedBitmapChecked
    have hrangeChecked :=
      indexedDataInRange_non8_full_of_coordinates bmp hpalSize hrange
    simpa [options] using
      encodeIndexedBitmapWithOptionsChecked_stored_eq_spec_bytes_non8
        bmp hw hh hbd hpalSize hrangeChecked htrans hbg
  have hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth :=
    entryCount_of_entries_size_paletteIndexLimit bmp.palette bmp.bitDepth hpalSize
  have hMetadata :=
    PaletteContainerSpec.decodeIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_data
      s bmp rfl rfl rfl hIdatSize hbd hpal hrange
  have hPixel :=
    PaletteContainerSpec.decodeIndexedBitmap_stored_encodeRawIndexed_none_non8_data
      s bmp rfl rfl rfl hIdatSize hbd hpal hrange
  exact ⟨s.bytes, hEncode, hMetadata, hPixel⟩

/-- Fixed-Huffman checked indexed encode succeeds, and both indexed decode APIs
recover the original index bytes for 1/2/4-bit full-addressable-palette
filter-0 inputs. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_fixed_non8_data
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (hIdatSize :
      (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)).size < 2 ^ 32) :
    ∃ bytes,
      encodeIndexedBitmapChecked bmp .fixed = Except.ok bytes ∧
        (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data) =
          some bmp.data ∧
        (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  let s := encodedSpecNon8 bmp
    (zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)) hw hh hbd hpalSize
  have hEncode :
      encodeIndexedBitmapChecked bmp .fixed = Except.ok s.bytes := by
    unfold encodeIndexedBitmapChecked
    have hrangeChecked :=
      indexedDataInRange_non8_full_of_coordinates bmp hpalSize hrange
    simpa [options] using
      encodeIndexedBitmapWithOptionsChecked_fixed_eq_spec_bytes_non8
        bmp hw hh hbd hpalSize hrangeChecked htrans hbg
  have hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth :=
    entryCount_of_entries_size_paletteIndexLimit bmp.palette bmp.bitDepth hpalSize
  have hMetadata :=
    PaletteContainerSpec.decodeIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_data
      s bmp rfl rfl rfl hIdatSize hbd hpal hrange
  have hPixel :=
    PaletteContainerSpec.decodeIndexedBitmap_fixed_encodeRawIndexed_none_non8_data
      s bmp rfl rfl rfl hIdatSize hbd hpal hrange
  exact ⟨s.bytes, hEncode, hMetadata, hPixel⟩

/-- Dynamic-Huffman checked indexed encode succeeds, and both indexed decode
APIs recover the original index bytes for 1/2/4-bit full-addressable-palette
filter-0 inputs. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_dynamic_non8_data
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (hIdatSize :
      (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size < 2 ^ 32) :
    ∃ bytes,
      encodeIndexedBitmapChecked bmp .dynamic = Except.ok bytes ∧
        (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data) =
          some bmp.data ∧
        (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data) = some bmp.data := by
  let s := encodedSpecNon8 bmp
    (zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)) hw hh hbd hpalSize
  have hEncode :
      encodeIndexedBitmapChecked bmp .dynamic = Except.ok s.bytes := by
    unfold encodeIndexedBitmapChecked
    have hrangeChecked :=
      indexedDataInRange_non8_full_of_coordinates bmp hpalSize hrange
    simpa [options] using
      encodeIndexedBitmapWithOptionsChecked_dynamic_eq_spec_bytes_non8
        bmp hw hh hbd hpalSize hrangeChecked htrans hbg
  have hpal : bmp.palette.entryCount = paletteIndexLimit bmp.bitDepth :=
    entryCount_of_entries_size_paletteIndexLimit bmp.palette bmp.bitDepth hpalSize
  have hMetadata :=
    PaletteContainerSpec.decodeIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_data
      s bmp rfl rfl rfl hIdatSize hbd hpal hrange
  have hPixel :=
    PaletteContainerSpec.decodeIndexedBitmap_dynamic_encodeRawIndexed_none_non8_data
      s bmp rfl rfl rfl hIdatSize hbd hpal hrange
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

/-- Checked indexed encode/decode round-trips 1/2/4-bit full-addressable-palette
filter-0 inputs for every supported compression mode. This is the packed-bit
counterpart to the existing 8-bit public encoder theorem. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_non8_data
    (mode : PngEncodeMode)
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth)
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
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_stored_non8_data
      bmp hw hh hbd hpalSize hrange htrans hbg hIdatSize
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_fixed_non8_data
      bmp hw hh hbd hpalSize hrange htrans hbg hIdatSize
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_dynamic_non8_data
      bmp hw hh hbd hpalSize hrange htrans hbg hIdatSize

/-- Checked indexed encode/decode round-trips every supported palette bit depth
when the explicit palette fills that bit depth's addressable index range. This
packages the 8-bit byte path and 1/2/4-bit packed path behind one theorem. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_supported_bitDepth_data
    (mode : PngEncodeMode)
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalSize : bmp.palette.entries.size = paletteIndexLimit bmp.bitDepth * 3)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat <
          paletteIndexLimit bmp.bitDepth)
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
  rcases hbd with hbd | hbd | hbd | hbd
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_non8_data
      mode bmp hw hh (Or.inl hbd) hpalSize hrange htrans hbg hIdatSize
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_non8_data
      mode bmp hw hh (Or.inr (Or.inl hbd)) hpalSize hrange htrans hbg hIdatSize
  · exact decodeIndexedBitmap_encodeIndexedBitmapChecked_non8_data
      mode bmp hw hh (Or.inr (Or.inr hbd)) hpalSize hrange htrans hbg hIdatSize
  · have hpalSize256 : bmp.palette.entries.size = 256 * 3 := by
      simpa [hbd, paletteIndexLimit] using hpalSize
    have hpal : bmp.palette.entryCount = 256 :=
      entryCount_of_entries_size_256 bmp.palette hpalSize256
    have hrangeChecked : indexedDataInRange bmp.data bmp.palette.entryCount = true := by
      have hchecked :
          indexedDataInRange bmp.data 256 = true := by
        apply PaletteValidation.indexedDataInRange_true_of_valid_coordinates
        intro y hy x hx
        simpa [hbd, paletteIndexLimit] using hrange y hy x hx
      simpa [hpal] using hchecked
    exact decodeIndexedBitmap_encodeIndexedBitmapChecked_8_256_data
      mode bmp hw hh hbd hpalSize256 hrangeChecked htrans hbg hIdatSize

/-- Checked indexed encode/decode round-trips every supported palette bit depth
for any explicit palette that fits the bit depth and contains every source
index. This generalizes the earlier full-addressable-palette theorem. -/
theorem decodeIndexedBitmap_encodeIndexedBitmapChecked_paletteRange_data
    (mode : PngEncodeMode)
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalNonempty : bmp.palette.entries.size ≠ 0)
    (hpalTriplets : bmp.palette.entries.size % 3 = 0)
    (hpalMax : bmp.palette.entries.size ≤ 256 * 3)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount)
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
  let idat :=
    match mode with
    | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
    | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
    | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)
  let s := encodedSpecPaletteRange bmp idat hw hh hbd hpalNonempty hpalTriplets
    hpalMax hpalFits
  have hrangeChecked : indexedDataInRange bmp.data bmp.palette.entryCount = true :=
    PaletteValidation.indexedDataInRange_true_of_valid_coordinates
      bmp bmp.palette.entryCount hrange
  have hEncode : encodeIndexedBitmapChecked bmp mode = Except.ok s.bytes := by
    unfold encodeIndexedBitmapChecked
    have hbytes :=
      encodeIndexedBitmapWithOptionsChecked_eq_spec_bytes_paletteRange
        mode bmp hw hh hbd hpalNonempty hpalTriplets hpalMax hpalFits
        hrangeChecked htrans hbg
    simpa [options, s, idat] using hbytes
  have hMetadata :=
    PaletteContainerSpec.decodeIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_data
      s bmp mode rfl rfl rfl hIdatSize hbd hpalFits hrange
  have hPixel :=
    PaletteContainerSpec.decodeIndexedBitmap_encodeRawIndexed_none_paletteRange_data
      s bmp mode rfl rfl rfl hIdatSize hbd hpalFits hrange
  exact ⟨s.bytes, hEncode, hMetadata, hPixel⟩

end PaletteEncoderRoundTrip

end Lemmas

end Bitmaps
