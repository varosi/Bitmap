import Bitmap.Png
import Bitmap.Lemmas.Png.Gray1
import Bitmap.Lemmas.Png.EncodeDecodeBase

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## PNG encoder filter helper facts

These facts document the public encoder-filter option surface and the default
filter-0 compatibility path. The full byte-for-byte default round-trip remains
the existing `decodeBitmap_encodeBitmap` theorem family. -/

private lemma foldl_filterPush_size
    (xs : List Nat) (f : Nat → UInt8) (out : ByteArray) :
    (xs.foldl (fun out i => out.push (f i)) out).size = out.size + xs.length := by
  induction xs generalizing out with
  | nil => simp
  | cons i xs ih =>
      have ih' := ih (out := out.push (f i))
      simpa [ByteArray.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'

/-- Every public encoder row filter maps to a PNG filter byte accepted by the
decoder. This is the validation fact used by fixed and adaptive strategy code. -/
@[simp] lemma pngRowFilter_toByte_valid (filter : PngRowFilter) :
    filter.toByte.toNat ≤ 4 := by
  cases filter <;> decide

/-- Filter `none` is byte-preserving at row level.
This pins the compatibility case shared by default and fixed-filter encoding. -/
@[simp] lemma filterRow_none (row prev : ByteArray) (bpp : Nat) :
    filterRow .none row prev bpp = row := by
  rfl

/-- Filtering a row preserves the row payload size.
This is the local size invariant needed before serializing filter bytes. -/
lemma filterRow_size (filter : PngRowFilter) (row prev : ByteArray) (bpp : Nat) :
    (filterRow filter row prev bpp).size = row.size := by
  cases filter with
  | none => rfl
  | sub =>
      unfold filterRow
      simp [Std.Legacy.Range.forIn_eq_forIn_range']
      simpa using foldl_filterPush_size (List.range' 0 row.size 1)
        (fun i => filterResidualByte (row.get! i) (filterRowPredictor .sub row prev bpp i))
        ByteArray.empty
  | up =>
      unfold filterRow
      simp [Std.Legacy.Range.forIn_eq_forIn_range']
      simpa using foldl_filterPush_size (List.range' 0 row.size 1)
        (fun i => filterResidualByte (row.get! i) (filterRowPredictor .up row prev bpp i))
        ByteArray.empty
  | average =>
      unfold filterRow
      simp [Std.Legacy.Range.forIn_eq_forIn_range']
      simpa using foldl_filterPush_size (List.range' 0 row.size 1)
        (fun i => filterResidualByte (row.get! i) (filterRowPredictor .average row prev bpp i))
        ByteArray.empty
  | paeth =>
      unfold filterRow
      simp [Std.Legacy.Range.forIn_eq_forIn_range']
      simpa using foldl_filterPush_size (List.range' 0 row.size 1)
        (fun i => filterResidualByte (row.get! i) (filterRowPredictor .paeth row prev bpp i))
        ByteArray.empty

/-- The option-level default strategy writes a filter-0 row without modifying
the row payload. This keeps existing option literals backward compatible. -/
@[simp] lemma filterRowForStrategy_none (row prev : ByteArray) (bpp : Nat) :
    filterRowForStrategy .none row prev bpp = (PngRowFilter.none.toByte, row) := by
  rfl

/-- A fixed `none` strategy is also filter-0 and byte-preserving.
This records that opt-in fixed filtering can explicitly request filter type 0. -/
@[simp] lemma filterRowForStrategy_fixed_none (row prev : ByteArray) (bpp : Nat) :
    filterRowForStrategy (.fixed .none) row prev bpp = (PngRowFilter.none.toByte, row) := by
  rfl

/-- A fixed row-filter strategy preserves row payload size after filtering.
This connects the option-facing API to the row-size invariant above. -/
lemma filterRowForStrategy_fixed_size (filter : PngRowFilter)
    (row prev : ByteArray) (bpp : Nat) :
    (filterRowForStrategy (.fixed filter) row prev bpp).2.size = row.size := by
  simp [filterRowForStrategy, filterRow_size]

/-- The generic bitmap filtered encoder delegates to the proven fast filter-0
path when filtering is left at its default. -/
@[simp] lemma encodeRawWithFilter_none {px : Type u} [Pixel px] (bmp : Bitmap px) :
    encodeRawWithFilter bmp .none = encodeRawFast bmp := by
  rfl

/-- The Gray1 filtered encoder delegates to the packed filter-0 encoder when
filtering is left at its default. -/
@[simp] lemma encodeRawGray1WithFilter_none (bmp : BitmapGray1) :
    encodeRawGray1WithFilter bmp .none = encodeRawGray1 bmp := by
  rfl

/-- Default filtered raw encoding has the same size theorem as the existing
filter-0 encoder. This is the bridge needed by round-trip clients that opt out. -/
lemma encodeRawWithFilter_none_size {px : Type u} [Pixel px] (bmp : Bitmap px) :
    (encodeRawWithFilter bmp .none).size =
      bmp.size.height * (bmp.size.width * Pixel.bytesPerPixel (α := px) + 1) := by
  rw [encodeRawWithFilter_none, encodeRawFast_eq]
  exact encodeRaw_size (bmp := bmp)

/-- Default filtered Gray1 raw encoding has the packed row size already proved
for the filter-0 Gray1 encoder. -/
lemma encodeRawGray1WithFilter_none_size (bmp : BitmapGray1) :
    (encodeRawGray1WithFilter bmp .none).size =
      bmp.size.height * (gray1RowBytes bmp.size.width + 1) := by
  simp [encodeRawGray1WithFilter_none, encodeRawGray1_size]

/-- Choosing an adaptive row filter always returns a public filter whose byte is
accepted by the decoder. This keeps adaptive selection inside the PNG 0..4 set. -/
lemma adaptiveFilterRow_toByte_valid (row prev : ByteArray) (bpp : Nat) :
    (adaptiveFilterRow row prev bpp).1.toByte.toNat ≤ 4 := by
  exact pngRowFilter_toByte_valid _

end Lemmas

end Bitmaps
