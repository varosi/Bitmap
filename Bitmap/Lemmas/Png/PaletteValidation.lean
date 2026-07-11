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

/-- The checked indexed encoder accepts any explicit indexed bitmap whose
dimensions, palette shape, palette-size bound, pixel indices, and optional
palette metadata satisfy the PNG color-type 3 validation rules. -/
lemma validateIndexedBitmap_accepts
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hpalNonempty : bmp.palette.entries.size ≠ 0)
    (hpalTriplets : bmp.palette.entries.size % 3 = 0)
    (hpalMax : bmp.palette.entries.size ≤ 256 * 3)
    (hpalFits : bmp.palette.entryCount ≤ paletteMaxEntriesForBitDepth bmp.bitDepth)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans :
      ∀ alpha, bmp.transparency = some alpha → alpha.size ≤ bmp.palette.entryCount)
    (hbg :
      ∀ idx, bmp.background = some idx → idx.toNat < bmp.palette.entryCount) :
    validateIndexedBitmap bmp = Except.ok () := by
  have hbdOk :
      (bmp.bitDepth != 1 && bmp.bitDepth != 2 && bmp.bitDepth != 4 && bmp.bitDepth != 8) =
        false := by
    rcases hbd with hbd | hbd | hbd | hbd <;> simp [hbd]
  have hnotWidth : ¬ bmp.size.width ≥ UInt32.size := Nat.not_le_of_gt hw
  have hnotHeight : ¬ bmp.size.height ≥ UInt32.size := Nat.not_le_of_gt hh
  have hnotEmpty : (bmp.palette.entries.size == 0) = false := by
    simp [hpalNonempty]
  have hgoodMod : (bmp.palette.entries.size % 3 != 0) = false := by
    simp [hpalTriplets]
  have hnotPalOver : ¬ bmp.palette.entries.size > 256 * 3 := Nat.not_lt_of_ge hpalMax
  have hnotEntryOver :
      ¬ bmp.palette.entryCount > paletteMaxEntriesForBitDepth bmp.bitDepth :=
    Nat.not_lt_of_ge hpalFits
  unfold validateIndexedBitmap
  cases htransOpt : bmp.transparency with
  | none =>
      cases hbgOpt : bmp.background with
      | none =>
          simp [hbdOk, hnotWidth, hnotHeight, hnotEmpty, hgoodMod, hnotPalOver,
            hnotEntryOver, hrange]
          rfl
      | some idx =>
          have hidxLt : idx.toNat < bmp.palette.entryCount := hbg idx hbgOpt
          have hnotIdx : ¬ idx.toNat ≥ bmp.palette.entryCount := Nat.not_le_of_gt hidxLt
          simp [hbdOk, hnotWidth, hnotHeight, hnotEmpty, hgoodMod, hnotPalOver,
            hnotEntryOver, hrange, hnotIdx]
          rfl
  | some alpha =>
      have halphaLe : alpha.size ≤ bmp.palette.entryCount := htrans alpha htransOpt
      have hnotAlpha : ¬ alpha.size > bmp.palette.entryCount := Nat.not_lt_of_ge halphaLe
      cases hbgOpt : bmp.background with
      | none =>
          simp [hbdOk, hnotWidth, hnotHeight, hnotEmpty, hgoodMod, hnotPalOver,
            hnotEntryOver, hrange, hnotAlpha]
          rfl
      | some idx =>
          have hidxLt : idx.toNat < bmp.palette.entryCount := hbg idx hbgOpt
          have hnotIdx : ¬ idx.toNat ≥ bmp.palette.entryCount := Nat.not_le_of_gt hidxLt
          simp [hbdOk, hnotWidth, hnotHeight, hnotEmpty, hgoodMod, hnotPalOver,
            hnotEntryOver, hrange, hnotAlpha, hnotIdx]
          rfl

/-- The checked indexed encoder accepts valid bitmaps when the palette-size
bound is stated with the decoder's packed-index limit helper. This keeps
encoder validation reusable with packed-row decoder invariants. -/
lemma validateIndexedBitmap_accepts_of_paletteIndexLimit
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hw : bmp.size.width < UInt32.size)
    (hh : bmp.size.height < UInt32.size)
    (hpalNonempty : bmp.palette.entries.size ≠ 0)
    (hpalTriplets : bmp.palette.entries.size % 3 = 0)
    (hpalMax : bmp.palette.entries.size ≤ 256 * 3)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange : indexedDataInRange bmp.data bmp.palette.entryCount = true)
    (htrans :
      ∀ alpha, bmp.transparency = some alpha → alpha.size ≤ bmp.palette.entryCount)
    (hbg :
      ∀ idx, bmp.background = some idx → idx.toNat < bmp.palette.entryCount) :
    validateIndexedBitmap bmp = Except.ok () := by
  exact validateIndexedBitmap_accepts bmp hbd hw hh hpalNonempty hpalTriplets hpalMax
    (by simpa [paletteMaxEntriesForBitDepth_eq_paletteIndexLimit] using hpalFits) hrange
    htrans hbg

/-- If every byte visited by the index-range loop is below the palette limit,
the loop leaves its Boolean accumulator true. This isolates the `forIn` shape of
`indexedDataInRange` from bitmap-level proofs. -/
private lemma indexedDataInRange_forIn_true (data : ByteArray) (limit : Nat) :
    ∀ l : List Nat, (∀ i, i ∈ l → (data.get! i).toNat < limit) →
      Id.run ((forIn (m := Id) l true fun i r =>
        have ok := r
        if (data.get! i).toNat ≥ limit then
          have ok := false
          do
          pure PUnit.unit
          pure (ForInStep.yield ok)
        else
          do
          pure PUnit.unit
          pure (ForInStep.yield ok)) : Id Bool) = true := by
  intro l
  induction l with
  | nil =>
      intro _
      simp
  | cons a t ih =>
      intro h
      have ha : ¬ (data.get! a).toNat ≥ limit := Nat.not_le_of_gt (h a (by simp))
      have ht : ∀ i, i ∈ t → (data.get! i).toNat < limit := by
        intro i hi
        exact h i (by simp [hi])
      simp [forIn, ha]
      simpa [forIn] using ih ht

/-- Pointwise byte bounds imply the checked indexed encoder's range predicate.
This turns a usable `∀ i < data.size` invariant into the Boolean validation
branch used by `validateIndexedBitmap`. -/
lemma indexedDataInRange_true_of_forall_get! (data : ByteArray) (limit : Nat)
    (h : ∀ i, i < data.size → (data.get! i).toNat < limit) :
    indexedDataInRange data limit = true := by
  unfold indexedDataInRange
  simpa using
    (indexedDataInRange_forIn_true data limit (List.range' 0 data.size) (by
      intro i hi
      apply h i
      rcases (List.mem_range'.mp hi) with ⟨j, hj, hij⟩
      omega))

/-- Coordinate-wise indexed bitmap bounds imply the checked encoder's range
predicate. The bitmap validity proof converts the flat byte loop back to
`y * width + x` coordinates. -/
lemma indexedDataInRange_true_of_valid_coordinates (bmp : PngIndexedBitmap) (limit : Nat)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < limit) :
    indexedDataInRange bmp.data limit = true := by
  apply indexedDataInRange_true_of_forall_get!
  intro i hi
  by_cases hwidth : bmp.size.width = 0
  · have hsize0 : bmp.data.size = 0 := by
      calc
        bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
        _ = 0 := by simp [hwidth]
    exfalso
    rw [hsize0] at hi
    exact Nat.not_lt_zero i hi
  · let y := i / bmp.size.width
    let x := i % bmp.size.width
    have hwidthPos : 0 < bmp.size.width := Nat.pos_of_ne_zero hwidth
    have hx : x < bmp.size.width := by
      simpa [x] using Nat.mod_lt i hwidthPos
    have hiPixels : i < bmp.size.width * bmp.size.height := by
      simpa [bmp.valid] using hi
    have hy : y < bmp.size.height := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.mul_comm] using hiPixels
    have hidx : y * bmp.size.width + x = i := by
      calc
        y * bmp.size.width + x = bmp.size.width * y + x := by rw [Nat.mul_comm]
        _ = i := by simpa [y, x] using Nat.div_add_mod i bmp.size.width
    simpa [hidx] using hrange y hy x hx

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

/-- pixel indices are validated against the palette entry count before raw rows
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
