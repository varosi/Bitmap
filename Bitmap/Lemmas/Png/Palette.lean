import Bitmap.Png

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette helper facts

These lemmas document the packed row geometry and bit-depth boundaries used by
PNG color type 3. They are focused helper coverage rather than a full container
theorem. -/

/-- A packed palette row uses the PNG/RFC byte count formula.
This pins the row-size helper shared by indexed encode and decode. -/
@[simp] lemma paletteRowBytes_eq (w bitDepth : Nat) :
    paletteRowBytes w bitDepth = (w * bitDepth + 7) / 8 := by
  rfl

/-- A 1-bit palette can address two entries.
This records the selected-palette-size boundary used by validation. -/
@[simp] lemma paletteIndexLimit_1 :
    paletteIndexLimit 1 = 2 := by
  rfl

/-- A 2-bit palette can address four entries.
This records the selected-palette-size boundary used by validation. -/
@[simp] lemma paletteIndexLimit_2 :
    paletteIndexLimit 2 = 4 := by
  rfl

/-- A 4-bit palette can address sixteen entries.
This records the selected-palette-size boundary used by validation. -/
@[simp] lemma paletteIndexLimit_4 :
    paletteIndexLimit 4 = 16 := by
  rfl

/-- An 8-bit palette can address all PNG palette entries.
This records the selected-palette-size boundary used by validation. -/
@[simp] lemma paletteIndexLimit_8 :
    paletteIndexLimit 8 = 256 := by
  rfl

/-- PNG row-byte calculation for 1-bit indexed rows matches `paletteRowBytes`.
This keeps parser-side row sizing aligned with indexed row packing. -/
lemma pngRowBytes_palette1 (w : Nat) :
    pngRowBytesForColorTypeAndBitDepth? w 3 1 = some (paletteRowBytes w 1) := by
  simp [pngRowBytesForColorTypeAndBitDepth?, pngBitsPerPixelForColorTypeAndBitDepth?,
    pngChannelCountForColorType?, paletteRowBytes]

/-- PNG row-byte calculation for 2-bit indexed rows matches `paletteRowBytes`.
This keeps parser-side row sizing aligned with indexed row packing. -/
lemma pngRowBytes_palette2 (w : Nat) :
    pngRowBytesForColorTypeAndBitDepth? w 3 2 = some (paletteRowBytes w 2) := by
  simp [pngRowBytesForColorTypeAndBitDepth?, pngBitsPerPixelForColorTypeAndBitDepth?,
    pngChannelCountForColorType?, paletteRowBytes]

/-- PNG row-byte calculation for 4-bit indexed rows matches `paletteRowBytes`.
This keeps parser-side row sizing aligned with indexed row packing. -/
lemma pngRowBytes_palette4 (w : Nat) :
    pngRowBytesForColorTypeAndBitDepth? w 3 4 = some (paletteRowBytes w 4) := by
  simp [pngRowBytesForColorTypeAndBitDepth?, pngBitsPerPixelForColorTypeAndBitDepth?,
    pngChannelCountForColorType?, paletteRowBytes]

/-- PNG row-byte calculation for 8-bit indexed rows matches `paletteRowBytes`.
This keeps parser-side row sizing aligned with indexed row packing. -/
lemma pngRowBytes_palette8 (w : Nat) :
    pngRowBytesForColorTypeAndBitDepth? w 3 8 = some (paletteRowBytes w 8) := by
  simp [pngRowBytesForColorTypeAndBitDepth?, pngBitsPerPixelForColorTypeAndBitDepth?,
    pngChannelCountForColorType?, paletteRowBytes]

end Lemmas

end Bitmaps
