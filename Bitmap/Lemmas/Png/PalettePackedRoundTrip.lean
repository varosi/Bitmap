import Bitmap.Png

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Packed indexed-palette public API examples

These computational theorems exercise the public checked indexed encoder and
both indexed decode APIs for packed 1-, 2-, and 4-bit palette rows.  They
complement the general 8-bit proof by pinning the packed paths end to end. -/

namespace PalettePackedRoundTrip

private def palette2 : PngPalette :=
  { entries := ByteArray.mk #[
      u8 0, u8 0, u8 0,
      u8 255, u8 255, u8 255] }

private def palette4 : PngPalette :=
  { entries := ByteArray.mk #[
      u8 0, u8 0, u8 0,
      u8 85, u8 0, u8 0,
      u8 0, u8 85, u8 0,
      u8 0, u8 0, u8 85] }

private def palette16 : PngPalette :=
  { entries := ByteArray.mk #[
      u8 0, u8 0, u8 0,
      u8 17, u8 0, u8 0,
      u8 34, u8 0, u8 0,
      u8 51, u8 0, u8 0,
      u8 68, u8 0, u8 0,
      u8 85, u8 0, u8 0,
      u8 102, u8 0, u8 0,
      u8 119, u8 0, u8 0,
      u8 136, u8 0, u8 0,
      u8 153, u8 0, u8 0,
      u8 170, u8 0, u8 0,
      u8 187, u8 0, u8 0,
      u8 204, u8 0, u8 0,
      u8 221, u8 0, u8 0,
      u8 238, u8 0, u8 0,
      u8 255, u8 0, u8 0] }

private def indexed1 : PngIndexedBitmap :=
  { size := { width := 8, height := 1 }
    bitDepth := 1
    palette := palette2
    data := ByteArray.mk #[u8 0, u8 1, u8 0, u8 1, u8 1, u8 0, u8 1, u8 0]
    transparency := none
    background := none
    valid := by native_decide }

private def indexed2 : PngIndexedBitmap :=
  { size := { width := 4, height := 1 }
    bitDepth := 2
    palette := palette4
    data := ByteArray.mk #[u8 0, u8 1, u8 2, u8 3]
    transparency := none
    background := none
    valid := by native_decide }

private def indexed4 : PngIndexedBitmap :=
  { size := { width := 4, height := 1 }
    bitDepth := 4
    palette := palette16
    data := ByteArray.mk #[u8 0, u8 3, u8 12, u8 15]
    transparency := none
    background := none
    valid := by native_decide }

private def indexed8 : PngIndexedBitmap :=
  { size := { width := 4, height := 1 }
    bitDepth := 8
    palette := palette16
    data := ByteArray.mk #[u8 0, u8 3, u8 12, u8 15]
    transparency := none
    background := none
    valid := by native_decide }

private def decodeIndexedDataAfterCheckedEncode
    (bmp : PngIndexedBitmap) (mode : PngEncodeMode) : Option ByteArray :=
  match encodeIndexedBitmapChecked bmp mode with
  | .ok bytes => (decodeIndexedBitmap bytes).map (fun bitmap => bitmap.data)
  | .error _ => none

private def decodeIndexedMetadataDataAfterCheckedEncode
    (bmp : PngIndexedBitmap) (mode : PngEncodeMode) : Option ByteArray :=
  match encodeIndexedBitmapChecked bmp mode with
  | .ok bytes =>
      (decodeIndexedBitmapWithMetadata bytes).map (fun result => result.bitmap.data)
  | .error _ => none

/-- For every supported PNG palette bit depth, there is an explicit indexed
bitmap whose checked encoder round-trips through both exact indexed decoders.
This quantifies over all compression modes and covers the packed 1/2/4-bit
paths plus the byte-wide 8-bit path. -/
theorem checked_roundtrip_fixture_for_supported_bitDepth
    (bitDepth : Nat) (mode : PngEncodeMode)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    ∃ bmp,
      bmp.bitDepth = bitDepth ∧
        decodeIndexedDataAfterCheckedEncode bmp mode = some bmp.data ∧
        decodeIndexedMetadataDataAfterCheckedEncode bmp mode = some bmp.data := by
  rcases hbd with rfl | rfl | rfl | rfl
  · refine ⟨indexed1, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed2, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed4, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide
  · refine ⟨indexed8, rfl, ?_, ?_⟩ <;> cases mode <;> native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 1-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_1bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed1 .stored = some indexed1.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed1 .stored = some indexed1.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 1-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_1bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed1 .fixed = some indexed1.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed1 .fixed = some indexed1.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 1-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_1bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed1 .dynamic = some indexed1.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed1 .dynamic = some indexed1.data := by
  native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 2-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_2bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed2 .stored = some indexed2.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed2 .stored = some indexed2.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 2-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_2bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed2 .fixed = some indexed2.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed2 .fixed = some indexed2.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 2-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_2bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed2 .dynamic = some indexed2.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed2 .dynamic = some indexed2.data := by
  native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 4-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_4bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed4 .stored = some indexed4.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed4 .stored = some indexed4.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 4-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_4bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed4 .fixed = some indexed4.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed4 .fixed = some indexed4.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 4-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_4bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed4 .dynamic = some indexed4.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed4 .dynamic = some indexed4.data := by
  native_decide

/-- Stored-zlib checked encode/decode round-trips a concrete 8-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_stored_8bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed8 .stored = some indexed8.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed8 .stored = some indexed8.data := by
  native_decide

/-- Fixed-Huffman checked encode/decode round-trips a concrete 8-bit indexed row
through both exact indexed decode APIs. -/
theorem checked_fixed_8bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed8 .fixed = some indexed8.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed8 .fixed = some indexed8.data := by
  native_decide

/-- Dynamic-Huffman checked encode/decode round-trips a concrete 8-bit indexed
row through both exact indexed decode APIs. -/
theorem checked_dynamic_8bit_fixture_data :
    decodeIndexedDataAfterCheckedEncode indexed8 .dynamic = some indexed8.data ∧
      decodeIndexedMetadataDataAfterCheckedEncode indexed8 .dynamic = some indexed8.data := by
  native_decide

end PalettePackedRoundTrip

end Lemmas

end Bitmaps
