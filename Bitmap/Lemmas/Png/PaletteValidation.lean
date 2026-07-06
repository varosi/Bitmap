import Bitmap.Lemmas.Png.Palette

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette encoder validation facts

These lemmas pin the checked indexed encoder's rejection surface.  They prove
that each validation branch reports the intended error before bytes are
emitted. -/

namespace PaletteValidation

/-- A failed indexed-bitmap validation is returned unchanged by the public
checked encoder API. This connects validation branch facts to API behavior. -/
lemma encodeIndexedBitmapWithOptionsChecked_rejects_of_validate_error
    (bmp : PngIndexedBitmap) (options : PngEncodeOptions) (msg : String)
    (hvalid : validateIndexedBitmap bmp = Except.error msg) :
    encodeIndexedBitmapWithOptionsChecked bmp options = Except.error msg := by
  unfold encodeIndexedBitmapWithOptionsChecked
  simp [hvalid]
  rfl

/-- The indexed encoder rejects bit depths outside PNG's 1/2/4/8 palette set. -/
lemma validateIndexedBitmap_rejects_bad_bitDepth (bmp : PngIndexedBitmap)
    (h1 : bmp.bitDepth ≠ 1) (h2 : bmp.bitDepth ≠ 2)
    (h4 : bmp.bitDepth ≠ 4) (h8 : bmp.bitDepth ≠ 8) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG bit depth must be 1, 2, 4, or 8" := by
  have hb1 : (bmp.bitDepth != 1) = true := by simp [h1]
  have hb2 : (bmp.bitDepth != 2) = true := by simp [h2]
  have hb4 : (bmp.bitDepth != 4) = true := by simp [h4]
  have hb8 : (bmp.bitDepth != 8) = true := by simp [h8]
  unfold validateIndexedBitmap
  simp [hb1, hb2, hb4, hb8]
  rfl

/-- Widths at or above the PNG u32 limit are rejected before encoding. -/
lemma validateIndexedBitmap_rejects_width_limit (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 8) (hw : bmp.size.width ≥ UInt32.size) :
    validateIndexedBitmap bmp =
      Except.error "bitmap width exceeds PNG limit (2^32)" := by
  unfold validateIndexedBitmap
  simp [hbd, hw]
  rfl

/-- Heights at or above the PNG u32 limit are rejected before encoding. -/
lemma validateIndexedBitmap_rejects_height_limit (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height ≥ UInt32.size) :
    validateIndexedBitmap bmp =
      Except.error "bitmap height exceeds PNG limit (2^32)" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hh]
  rfl

/-- Empty palettes are rejected because indexed PNGs require at least one PLTE
entry. -/
lemma validateIndexedBitmap_rejects_empty_palette (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hpal : bmp.palette.entries.size = 0) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG palette must not be empty" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hpal]
  rfl

/-- Palette byte payloads must be RGB triplets, so non-multiples of three are
rejected before compression. -/
lemma validateIndexedBitmap_rejects_bad_palette_length (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hnonempty : bmp.palette.entries.size ≠ 0)
    (hmod : bmp.palette.entries.size % 3 ≠ 0) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG palette byte size must be a multiple of 3" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  have hnotEmpty : (bmp.palette.entries.size == 0) = false := by
    simp [hnonempty]
  have hbadMod : (bmp.palette.entries.size % 3 != 0) = true := by
    simp [hmod]
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hnotEmpty, hbadMod]
  rfl

/-- PNG palettes have at most 256 RGB entries; larger aligned payloads are
rejected. -/
lemma validateIndexedBitmap_rejects_palette_oversize (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (htriplets : bmp.palette.entries.size % 3 = 0)
    (hover : bmp.palette.entries.size > 256 * 3) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG palette has more than 256 entries" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  have hnonempty : bmp.palette.entries.size ≠ 0 := by omega
  have hnotEmpty : (bmp.palette.entries.size == 0) = false := by
    simp [hnonempty]
  have hgoodMod : (bmp.palette.entries.size % 3 != 0) = false := by
    simp [htriplets]
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hnotEmpty, hgoodMod, hover]
  rfl

/-- A 1-bit indexed image cannot encode three palette entries because only two
indices are representable. -/
lemma validateIndexedBitmap_rejects_palette_too_large_for_depth1
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hpal : bmp.palette.entries.size = 3 * 3) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG palette is too large for the selected bit depth" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hpal, PngPalette.entryCount,
    paletteMaxEntriesForBitDepth]
  rfl

/-- Pixel indices are validated against the palette entry count before raw rows
are packed. -/
lemma validateIndexedBitmap_rejects_out_of_range_indices
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hpal : bmp.palette.entries.size = 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = false) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG pixel data contains an out-of-range palette index" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  have hcount : bmp.palette.entryCount = 1 := by
    simp [PngPalette.entryCount, hpal]
  have hrange1 : indexedDataInRange bmp.data 1 = false := by
    simpa [hcount] using hrange
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hpal, hcount, hrange1,
    paletteMaxEntriesForBitDepth]
  rfl

/-- Palette alpha data cannot be longer than PLTE, so overlong `tRNS` metadata
is rejected by the checked encoder. -/
lemma validateIndexedBitmap_rejects_alpha_too_long
    (bmp : PngIndexedBitmap) (alpha : ByteArray)
    (hbd : bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hpal : bmp.palette.entries.size = 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = some alpha)
    (halpha : alpha.size > bmp.palette.entryCount) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG palette alpha data is longer than the palette" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  have hcount : bmp.palette.entryCount = 1 := by
    simp [PngPalette.entryCount, hpal]
  have hrange1 : indexedDataInRange bmp.data 1 = true := by
    simpa [hcount] using hrange
  have halpha1 : alpha.size > 1 := by
    simpa [hcount] using halpha
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hpal, hcount, hrange1, htrans, halpha1,
    paletteMaxEntriesForBitDepth]
  rfl

/-- Palette background metadata must name an existing palette entry. -/
lemma validateIndexedBitmap_rejects_background_out_of_range
    (bmp : PngIndexedBitmap) (idx : UInt8)
    (hbd : bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hpal : bmp.palette.entries.size = 3)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = some idx)
    (hidx : idx.toNat ≥ bmp.palette.entryCount) :
    validateIndexedBitmap bmp =
      Except.error "indexed PNG background index is outside the palette" := by
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  have hcount : bmp.palette.entryCount = 1 := by
    simp [PngPalette.entryCount, hpal]
  have hrange1 : indexedDataInRange bmp.data 1 = true := by
    simpa [hcount] using hrange
  have hidx1 : idx.toNat ≥ 1 := by
    simpa [hcount] using hidx
  unfold validateIndexedBitmap
  simp [hbd, hnotWidth, hnotHeight, hpal, hcount, hrange1, htrans, hbg, hidx1,
    paletteMaxEntriesForBitDepth]
  rfl

end PaletteValidation

end Lemmas

end Bitmaps
