import Bitmap.Png
import Bitmap.Lemmas.Png.EncodeFilter

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Indexed-palette helper facts

These lemmas document the packed row geometry and bit-depth boundaries used by
PNG color type 3. They are focused helper coverage rather than a full container
theorem. -/

private lemma byteArray_size_set! (row : ByteArray) (i : Nat) (v : UInt8) :
    (row.set! i v).size = row.size := by
  cases row with
  | mk arr =>
      simp [ByteArray.set!, ByteArray.size, Array.setIfInBounds]
      by_cases h : i < arr.size
      · simp [h, Array.size_set]
      · simp [h]

private lemma byteArray_get!_set!_self (row : ByteArray) (i : Nat) (v : UInt8)
    (hi : i < row.size) :
    (row.set! i v).get! i = v := by
  cases row with
  | mk arr =>
      have hi' : i < arr.size := by simpa [ByteArray.size] using hi
      simp [ByteArray.set!, ByteArray.get!, Array.setIfInBounds, hi']

private lemma byteArray_get!_set!_ne (row : ByteArray) (i j : Nat) (v : UInt8)
    (hij : i ≠ j) :
    (row.set! i v).get! j = row.get! j := by
  cases row with
  | mk arr =>
      simp [ByteArray.set!, ByteArray.get!, Array.setIfInBounds]
      by_cases hi : i < arr.size
      · by_cases hj : j < arr.size
        · simp [hi, hj, Array.getElem_set_ne (xs := arr) (i := i) (j := j)
            (h' := hi) (pj := hj) (h := hij)]
        · simp [hi, hj]
      · simp [hi]

private lemma byteArray_get!_replicate_zero (rowBytes i : Nat) :
    (ByteArray.mk <| Array.replicate rowBytes (0 : UInt8)).get! i = 0 := by
  simp [ByteArray.get!]
  by_cases h : i < (Array.replicate rowBytes (0 : UInt8)).size
  · rw [getElem!_pos (Array.replicate rowBytes (0 : UInt8)) i h]
    simp
  · rw [getElem!_neg (Array.replicate rowBytes (0 : UInt8)) i h]
    rfl

private lemma u8_toNat_of_lt (n : Nat) (h : n < 256) :
    (u8 n).toNat = n := by
  simpa [u8, UInt8.size] using
    UInt8.toNat_ofNat_of_lt' (n := n) (by simpa [UInt8.size] using h)

private lemma u8_mod_toNat_lt (n limit : Nat) (hpos : 0 < limit) (hlimit : limit ≤ 256) :
    (u8 (n % limit)).toNat < limit := by
  have hmod : n % limit < limit := Nat.mod_lt n hpos
  have hmod256 : n % limit < 256 := Nat.lt_of_lt_of_le hmod hlimit
  rw [u8_toNat_of_lt (n % limit) hmod256]
  exact hmod

private lemma u8_toNat_eq_self (sample : UInt8) :
    u8 sample.toNat = sample := by
  have hs : sample.toNat < 256 := by
    simpa using UInt8.toNat_lt sample
  exact UInt8.toNat.inj (u8_toNat_of_lt sample.toNat hs)

private lemma packedFieldWriteSame1 (old idx : UInt8) (r : Nat)
    (hr : r < 8) (hidx : idx.toNat < 2)
    (hzero : (old.toNat >>> (7 - r)) % 2 = 0) :
    u8 (((u8 (old.toNat ||| ((idx.toNat % 2) <<< (7 - r)))).toNat >>> (7 - r)) % 2) =
      idx := by
  have h :
      ∀ old idx : Fin 256, ∀ r : Fin 8,
        idx.val < 2 →
        (old.val >>> (7 - r.val)) % 2 = 0 →
        u8 (((u8 (old.val ||| ((idx.val % 2) <<< (7 - r.val)))).toNat >>>
          (7 - r.val)) % 2) = u8 idx.val := by
    native_decide
  simpa [u8_toNat_eq_self idx] using
    h ⟨old.toNat, UInt8.toNat_lt old⟩ ⟨idx.toNat, UInt8.toNat_lt idx⟩ ⟨r, hr⟩
      hidx hzero

private lemma packedFieldWriteSame2 (old idx : UInt8) (r : Nat)
    (hr : r < 4) (hidx : idx.toNat < 4)
    (hzero : (old.toNat >>> (6 - 2 * r)) % 4 = 0) :
    u8 (((u8 (old.toNat ||| ((idx.toNat % 4) <<< (6 - 2 * r)))).toNat >>>
      (6 - 2 * r)) % 4) = idx := by
  have h :
      ∀ old idx : Fin 256, ∀ r : Fin 4,
        idx.val < 4 →
        (old.val >>> (6 - 2 * r.val)) % 4 = 0 →
        u8 (((u8 (old.val ||| ((idx.val % 4) <<< (6 - 2 * r.val)))).toNat >>>
          (6 - 2 * r.val)) % 4) = u8 idx.val := by
    native_decide
  simpa [u8_toNat_eq_self idx] using
    h ⟨old.toNat, UInt8.toNat_lt old⟩ ⟨idx.toNat, UInt8.toNat_lt idx⟩ ⟨r, hr⟩
      hidx hzero

private lemma packedFieldWriteSame4 (old idx : UInt8) (r : Nat)
    (hr : r < 2) (hidx : idx.toNat < 16)
    (hzero : (old.toNat >>> (4 - 4 * r)) % 16 = 0) :
    u8 (((u8 (old.toNat ||| ((idx.toNat % 16) <<< (4 - 4 * r)))).toNat >>>
      (4 - 4 * r)) % 16) = idx := by
  have h :
      ∀ old idx : Fin 256, ∀ r : Fin 2,
        idx.val < 16 →
        (old.val >>> (4 - 4 * r.val)) % 16 = 0 →
        u8 (((u8 (old.val ||| ((idx.val % 16) <<< (4 - 4 * r.val)))).toNat >>>
          (4 - 4 * r.val)) % 16) = u8 idx.val := by
    native_decide
  simpa [u8_toNat_eq_self idx] using
    h ⟨old.toNat, UInt8.toNat_lt old⟩ ⟨idx.toNat, UInt8.toNat_lt idx⟩ ⟨r, hr⟩
      hidx hzero

private lemma packedFieldWriteOther1 (old idx : UInt8) (r s : Nat)
    (hr : r < 8) (hs : s < 8) (hne : r ≠ s) :
    u8 (((u8 (old.toNat ||| ((idx.toNat % 2) <<< (7 - r)))).toNat >>> (7 - s)) % 2) =
      u8 ((old.toNat >>> (7 - s)) % 2) := by
  have h :
      ∀ old idx : Fin 256, ∀ r s : Fin 8,
        r.val ≠ s.val →
        u8 (((u8 (old.val ||| ((idx.val % 2) <<< (7 - r.val)))).toNat >>>
          (7 - s.val)) % 2) =
          u8 ((old.val >>> (7 - s.val)) % 2) := by
    native_decide
  exact
    h ⟨old.toNat, UInt8.toNat_lt old⟩ ⟨idx.toNat, UInt8.toNat_lt idx⟩ ⟨r, hr⟩ ⟨s, hs⟩ hne

private lemma packedFieldWriteOther2 (old idx : UInt8) (r s : Nat)
    (hr : r < 4) (hs : s < 4) (hne : r ≠ s) :
    u8 (((u8 (old.toNat ||| ((idx.toNat % 4) <<< (6 - 2 * r)))).toNat >>>
      (6 - 2 * s)) % 4) =
      u8 ((old.toNat >>> (6 - 2 * s)) % 4) := by
  have h :
      ∀ old idx : Fin 256, ∀ r s : Fin 4,
        r.val ≠ s.val →
        u8 (((u8 (old.val ||| ((idx.val % 4) <<< (6 - 2 * r.val)))).toNat >>>
          (6 - 2 * s.val)) % 4) =
          u8 ((old.val >>> (6 - 2 * s.val)) % 4) := by
    native_decide
  exact
    h ⟨old.toNat, UInt8.toNat_lt old⟩ ⟨idx.toNat, UInt8.toNat_lt idx⟩ ⟨r, hr⟩ ⟨s, hs⟩ hne

private lemma packedFieldWriteOther4 (old idx : UInt8) (r s : Nat)
    (hr : r < 2) (hs : s < 2) (hne : r ≠ s) :
    u8 (((u8 (old.toNat ||| ((idx.toNat % 16) <<< (4 - 4 * r)))).toNat >>>
      (4 - 4 * s)) % 16) =
      u8 ((old.toNat >>> (4 - 4 * s)) % 16) := by
  have h :
      ∀ old idx : Fin 256, ∀ r s : Fin 2,
        r.val ≠ s.val →
        u8 (((u8 (old.val ||| ((idx.val % 16) <<< (4 - 4 * r.val)))).toNat >>>
          (4 - 4 * s.val)) % 16) =
          u8 ((old.val >>> (4 - 4 * s.val)) % 16) := by
    native_decide
  exact
    h ⟨old.toNat, UInt8.toNat_lt old⟩ ⟨idx.toNat, UInt8.toNat_lt idx⟩ ⟨r, hr⟩ ⟨s, hs⟩ hne

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

/-- Encoder palette-capacity validation and decoder packed-index bounds use the
same limit for every bit depth. This keeps the two helper APIs aligned. -/
lemma paletteMaxEntriesForBitDepth_eq_paletteIndexLimit (bitDepth : Nat) :
    paletteMaxEntriesForBitDepth bitDepth = paletteIndexLimit bitDepth := by
  unfold paletteMaxEntriesForBitDepth paletteIndexLimit
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

/-- A 1-bit indexed row packs eight palette indices per byte.
This records the concrete packed-row size used by encoder and decoder proofs. -/
lemma paletteRowBytes_1 (w : Nat) :
    paletteRowBytes w 1 = (w + 7) / 8 := by
  unfold paletteRowBytes
  omega

/-- A 2-bit indexed row packs four palette indices per byte.
This records the concrete packed-row size used by encoder and decoder proofs. -/
lemma paletteRowBytes_2 (w : Nat) :
    paletteRowBytes w 2 = (w + 3) / 4 := by
  unfold paletteRowBytes
  omega

/-- A 4-bit indexed row packs two palette indices per byte.
This records the concrete packed-row size used by encoder and decoder proofs. -/
lemma paletteRowBytes_4 (w : Nat) :
    paletteRowBytes w 4 = (w + 1) / 2 := by
  unfold paletteRowBytes
  omega

/-- An 8-bit indexed row stores exactly one byte per pixel.
This reduces the packed-index path to the existing byte-row raw proofs. -/
lemma paletteRowBytes_8 (w : Nat) :
    paletteRowBytes w 8 = w := by
  unfold paletteRowBytes
  omega

/-- A full 256-entry 8-bit palette accepts every possible byte index.
This exposes the direct row-copy branch used by indexed raw round-trip proofs. -/
lemma paletteScatterFullRow_8_256 (row flat : ByteArray) (w y : Nat) :
    paletteScatterFullRow row flat w 8 y 256 =
      some (row.copySlice 0 flat (y * w) w) := by
  simp [paletteScatterFullRow]

/-- An Adam7 palette scatter with no pass pixels leaves the flat index buffer
unchanged. This pins the zero-width pass behavior used by Adam7 decoding. -/
lemma adam7ScatterRowPalette_empty_width
    (row flat : ByteArray) (w bitDepth paletteEntries : Nat)
    (pass : Adam7Pass) (passY : Nat) :
    adam7ScatterRowPalette row flat w bitDepth paletteEntries pass passY 0 =
      some flat := by
  simp [adam7ScatterRowPalette, adam7ScatterRowPaletteLoop]

/-- Decoding zero palette rows for one Adam7 pass consumes no bytes and leaves
the flat index buffer unchanged. This is the pass-loop base case. -/
lemma decodeAdam7PalettePassRows_empty_height
    (raw : ByteArray) (w bitDepth paletteEntries : Nat)
    (pass : Adam7Pass) (passWidth passY offset : Nat)
    (prevRow flat : ByteArray) :
    decodeAdam7PalettePassRows raw w bitDepth paletteEntries pass passWidth 0
      passY offset prevRow flat = some (offset, flat) := by
  simp [decodeAdam7PalettePassRows]

/-- With no Adam7 passes left, palette pass decoding returns the accumulated
offset and flat index buffer unchanged. This records the dispatcher base case. -/
lemma decodeAdam7PalettePasses_nil
    (raw flat : ByteArray) (w h bitDepth paletteEntries offset : Nat) :
    decodeAdam7PalettePasses raw w h bitDepth paletteEntries offset flat [] =
      some (offset, flat) := by
  rfl

/-- Reading a packed palette index is always within the addressable range for
the selected PNG bit depth. This is the core per-sample safety fact for
arbitrary packed 1/2/4/8-bit palette rows. -/
lemma palettePackedIndexAt_lt_indexLimit (row : ByteArray) (bitDepth x : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    (palettePackedIndexAt row bitDepth x).toNat < paletteIndexLimit bitDepth := by
  rcases hbd with rfl | rfl | rfl | rfl
  · unfold palettePackedIndexAt
    simp [paletteIndexLimit, palettePackedShift, u8_mod_toNat_lt]
  · unfold palettePackedIndexAt
    simp [paletteIndexLimit, palettePackedShift, u8_mod_toNat_lt]
  · unfold palettePackedIndexAt
    simp [paletteIndexLimit, palettePackedShift, u8_mod_toNat_lt]
  · unfold palettePackedIndexAt
    simpa [paletteIndexLimit] using UInt8.toNat_lt (row.get! x)

/-- If a palette has at least the bit-depth-addressable number of entries, any
packed index read from a row is a valid palette lookup. This is the row-local
range condition used by packed palette decoding. -/
lemma palettePackedIndexAt_lt_entries (row : ByteArray) (bitDepth x entries : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hentries : paletteIndexLimit bitDepth ≤ entries) :
    (palettePackedIndexAt row bitDepth x).toNat < entries :=
  Nat.lt_of_lt_of_le (palettePackedIndexAt_lt_indexLimit row bitDepth x hbd) hentries

private lemma paletteScatterFullRowLoop_succeeds_of_indexLimit
    (row flat : ByteArray) (w bitDepth y paletteEntries x : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hentries : paletteIndexLimit bitDepth ≤ paletteEntries) :
    ∃ flat',
      paletteScatterFullRowLoop row flat w bitDepth y paletteEntries x true = some flat' := by
  have hk :
      ∀ k, ∀ x flat,
        w - x = k →
        ∃ flat',
          paletteScatterFullRowLoop row flat w bitDepth y paletteEntries x true = some flat' := by
    intro k
    induction k with
    | zero =>
        intro x flat hk
        have hx : w ≤ x := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ x < w := not_lt_of_ge hx
        exact ⟨flat, by simp [paletteScatterFullRowLoop, hlt]⟩
    | succ k ih =>
        intro x flat hk
        have hlt : x < w := Nat.lt_of_sub_eq_succ hk
        have hidx :
            (palettePackedIndexAt row bitDepth x).toNat < paletteEntries :=
          palettePackedIndexAt_lt_entries row bitDepth x paletteEntries hbd hentries
        have hflag :
            (!decide (paletteEntries ≤ (palettePackedIndexAt row bitDepth x).toNat)) = true := by
          simp [Nat.not_le_of_gt hidx]
        have hk' : w - (x + 1) = k := by
          have hsum : w = Nat.succ k + x := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            w - (x + 1) = (Nat.succ k + x) - (x + 1) := by simp [hsum]
            _ = k := by omega
        rcases ih (x := x + 1)
          (flat := flat.set! (y * w + x) (palettePackedIndexAt row bitDepth x)) hk' with
          ⟨out, hout⟩
        refine ⟨out, ?_⟩
        rw [paletteScatterFullRowLoop.eq_1]
        simp [hlt, hflag, hout]
  exact hk (w - x) x flat rfl

/-- Full-row palette scatter succeeds for arbitrary supported packed rows when
the palette has every entry addressable by the selected bit depth. This hardens
the non-interlaced indexed decoder against false out-of-range failures. -/
lemma paletteScatterFullRow_succeeds_of_indexLimit
    (row flat : ByteArray) (w bitDepth y paletteEntries : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hentries : paletteIndexLimit bitDepth ≤ paletteEntries) :
    ∃ flat', paletteScatterFullRow row flat w bitDepth y paletteEntries = some flat' := by
  unfold paletteScatterFullRow
  by_cases hfast : bitDepth = 8 ∧ 256 ≤ paletteEntries
  · exact ⟨row.copySlice 0 flat (y * w) w, by simp [hfast]⟩
  · simp [hfast]
    exact
      paletteScatterFullRowLoop_succeeds_of_indexLimit row flat w bitDepth y
        paletteEntries 0 hbd hentries

private lemma adam7ScatterRowPaletteLoop_succeeds_of_indexLimit
    (row flat : ByteArray) (w bitDepth paletteEntries : Nat)
    (pass : Adam7Pass) (passY passX passWidth : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hentries : paletteIndexLimit bitDepth ≤ paletteEntries) :
    ∃ flat',
      adam7ScatterRowPaletteLoop row flat w bitDepth paletteEntries pass passY passX
        passWidth true = some flat' := by
  have hk :
      ∀ k, ∀ passX flat,
        passWidth - passX = k →
        ∃ flat',
          adam7ScatterRowPaletteLoop row flat w bitDepth paletteEntries pass passY passX
            passWidth true = some flat' := by
    intro k
    induction k with
    | zero =>
        intro passX flat hk
        have hx : passWidth ≤ passX := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ passX < passWidth := not_lt_of_ge hx
        exact ⟨flat, by simp [adam7ScatterRowPaletteLoop, hlt]⟩
    | succ k ih =>
        intro passX flat hk
        have hlt : passX < passWidth := Nat.lt_of_sub_eq_succ hk
        have hidx :
            (palettePackedIndexAt row bitDepth passX).toNat < paletteEntries :=
          palettePackedIndexAt_lt_entries row bitDepth passX paletteEntries hbd hentries
        have hflag :
            (!decide (paletteEntries ≤ (palettePackedIndexAt row bitDepth passX).toNat)) =
              true := by
          simp [Nat.not_le_of_gt hidx]
        have hk' : passWidth - (passX + 1) = k := by
          have hsum : passWidth = Nat.succ k + passX :=
            Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            passWidth - (passX + 1) =
                (Nat.succ k + passX) - (passX + 1) := by simp [hsum]
            _ = k := by omega
        rcases ih (passX := passX + 1)
          (flat :=
            flat.set! ((pass.startY + passY * pass.stepY) * w +
              (pass.startX + passX * pass.stepX))
              (palettePackedIndexAt row bitDepth passX)) hk' with
          ⟨out, hout⟩
        refine ⟨out, ?_⟩
        rw [adam7ScatterRowPaletteLoop.eq_1]
        simp [hlt, hflag, hout]
  exact hk (passWidth - passX) passX flat rfl

/-- Adam7 palette row scatter succeeds for arbitrary supported packed rows when
the palette has every entry addressable by the selected bit depth. This replaces
fixture-only coverage of the interlaced packed-index range check. -/
lemma adam7ScatterRowPalette_succeeds_of_indexLimit
    (row flat : ByteArray) (w bitDepth paletteEntries : Nat)
    (pass : Adam7Pass) (passY passWidth : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hentries : paletteIndexLimit bitDepth ≤ paletteEntries) :
    ∃ flat',
      adam7ScatterRowPalette row flat w bitDepth paletteEntries pass passY passWidth =
        some flat' := by
  simpa [adam7ScatterRowPalette] using
    adam7ScatterRowPaletteLoop_succeeds_of_indexLimit row flat w bitDepth paletteEntries pass
      passY 0 passWidth hbd hentries

private def adam7PaletteDstIndex (w : Nat) (pass : Adam7Pass) (passY passX : Nat) : Nat :=
  (pass.startY + passY * pass.stepY) * w + (pass.startX + passX * pass.stepX)

private lemma adam7PaletteDstIndex_ne_of_ne
    (w : Nat) (pass : Adam7Pass) (passY x y : Nat)
    (hstep : 0 < pass.stepX) (hne : x ≠ y) :
    adam7PaletteDstIndex w pass passY x ≠ adam7PaletteDstIndex w pass passY y := by
  intro h
  have h1 :
      pass.startX + x * pass.stepX = pass.startX + y * pass.stepX := by
    exact Nat.add_left_cancel h
  have hmul : x * pass.stepX = y * pass.stepX := by
    exact Nat.add_left_cancel h1
  exact hne (Nat.mul_right_cancel hstep hmul)

private lemma adam7ScatterRowPaletteLoop_get!_of_indexLimit
    (row flat : ByteArray) (w bitDepth paletteEntries : Nat)
    (pass : Adam7Pass) (passY passX passWidth watchX : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hentries : paletteIndexLimit bitDepth ≤ paletteEntries)
    (hstep : 0 < pass.stepX)
    (hdst : ∀ x, x < passWidth →
      adam7PaletteDstIndex w pass passY x < flat.size) :
    ∃ out,
      adam7ScatterRowPaletteLoop row flat w bitDepth paletteEntries pass passY passX
        passWidth true = some out ∧
      (if watchX < passX then
        out.get! (adam7PaletteDstIndex w pass passY watchX) =
          flat.get! (adam7PaletteDstIndex w pass passY watchX)
      else if watchX < passWidth then
        out.get! (adam7PaletteDstIndex w pass passY watchX) =
          palettePackedIndexAt row bitDepth watchX
      else
        out.get! (adam7PaletteDstIndex w pass passY watchX) =
          flat.get! (adam7PaletteDstIndex w pass passY watchX)) := by
  have hk :
      ∀ k, ∀ passX flat,
        passWidth - passX = k →
        (∀ x, x < passWidth →
          adam7PaletteDstIndex w pass passY x < flat.size) →
        ∃ out,
          adam7ScatterRowPaletteLoop row flat w bitDepth paletteEntries pass passY passX
            passWidth true = some out ∧
          (if watchX < passX then
            out.get! (adam7PaletteDstIndex w pass passY watchX) =
              flat.get! (adam7PaletteDstIndex w pass passY watchX)
          else if watchX < passWidth then
            out.get! (adam7PaletteDstIndex w pass passY watchX) =
              palettePackedIndexAt row bitDepth watchX
          else
            out.get! (adam7PaletteDstIndex w pass passY watchX) =
              flat.get! (adam7PaletteDstIndex w pass passY watchX)) := by
    intro k
    induction k with
    | zero =>
        intro passX flat hk hdst
        have hx : passWidth ≤ passX := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ passX < passWidth := not_lt_of_ge hx
        refine ⟨flat, ?_, ?_⟩
        · simp [adam7ScatterRowPaletteLoop, hlt]
        · by_cases hwatch : watchX < passX
          · simp [hwatch]
          · have hnotWidth : ¬ watchX < passWidth := fun h => hwatch (lt_of_lt_of_le h hx)
            simp [hwatch, hnotWidth]
    | succ k ih =>
        intro passX flat hk hdst
        have hlt : passX < passWidth := Nat.lt_of_sub_eq_succ hk
        have hidx :
            (palettePackedIndexAt row bitDepth passX).toNat < paletteEntries :=
          palettePackedIndexAt_lt_entries row bitDepth passX paletteEntries hbd hentries
        have hflag :
            (!decide (paletteEntries ≤ (palettePackedIndexAt row bitDepth passX).toNat)) =
              true := by
          simp [Nat.not_le_of_gt hidx]
        let dst := adam7PaletteDstIndex w pass passY passX
        let idx := palettePackedIndexAt row bitDepth passX
        let flat' := flat.set! dst idx
        have hdstPass : dst < flat.size := by
          simpa [dst] using hdst passX hlt
        have hdst' :
            ∀ x, x < passWidth →
              adam7PaletteDstIndex w pass passY x < flat'.size := by
          intro x hx
          simpa [flat', byteArray_size_set!] using hdst x hx
        have hk' : passWidth - (passX + 1) = k := by
          have hsum : passWidth = Nat.succ k + passX :=
            Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            passWidth - (passX + 1) =
                (Nat.succ k + passX) - (passX + 1) := by simp [hsum]
            _ = k := by omega
        rcases ih (passX := passX + 1) (flat := flat') hk' hdst' with
          ⟨out, hout, hget⟩
        refine ⟨out, ?_, ?_⟩
        · rw [adam7ScatterRowPaletteLoop.eq_1]
          simpa [hlt, hflag, dst, idx, flat', adam7PaletteDstIndex] using hout
        · by_cases hltWatch : watchX < passX
          · have hltWatchSucc : watchX < passX + 1 := Nat.lt_trans hltWatch (Nat.lt_succ_self _)
            have hne : dst ≠ adam7PaletteDstIndex w pass passY watchX := by
              exact adam7PaletteDstIndex_ne_of_ne w pass passY passX watchX hstep
                (by omega)
            have hflat' :
                flat'.get! (adam7PaletteDstIndex w pass passY watchX) =
                  flat.get! (adam7PaletteDstIndex w pass passY watchX) := by
              simpa [flat', dst, idx] using
                byteArray_get!_set!_ne flat dst (adam7PaletteDstIndex w pass passY watchX)
                  idx hne
            simp [hltWatch, hltWatchSucc] at hget ⊢
            exact hget.trans hflat'
          · have hgeWatch : passX ≤ watchX := Nat.le_of_not_lt hltWatch
            by_cases heq : watchX = passX
            · subst watchX
              have hltSucc : passX < passX + 1 := Nat.lt_succ_self passX
              have hcurrent :
                  flat'.get! dst = idx := by
                exact byteArray_get!_set!_self flat dst idx hdstPass
              simp [hltWatch, hltSucc, hlt] at hget ⊢
              exact hget.trans hcurrent
            · have hsucc : passX + 1 ≤ watchX := by omega
              have hnotSucc : ¬ watchX < passX + 1 := not_lt_of_ge hsucc
              by_cases hwatchWidth : watchX < passWidth
              · simp [hltWatch, hnotSucc, hwatchWidth] at hget ⊢
                exact hget
              · have hne : dst ≠ adam7PaletteDstIndex w pass passY watchX := by
                  exact adam7PaletteDstIndex_ne_of_ne w pass passY passX watchX hstep
                    (by omega)
                have hflat' :
                    flat'.get! (adam7PaletteDstIndex w pass passY watchX) =
                      flat.get! (adam7PaletteDstIndex w pass passY watchX) := by
                  simpa [flat', dst, idx] using
                    byteArray_get!_set!_ne flat dst
                      (adam7PaletteDstIndex w pass passY watchX) idx hne
                simp [hltWatch, hnotSucc, hwatchWidth] at hget ⊢
                exact hget.trans hflat'
  exact hk (passWidth - passX) passX flat rfl hdst

/-- Adam7 palette scatter writes each in-bounds pass-local sample to its exact
destination coordinate for arbitrary supported packed rows. This is the
symbolic exactness counterpart to the Adam7 scatter success lemma. -/
lemma adam7ScatterRowPalette_get!_of_indexLimit
    (row flat : ByteArray) (w bitDepth paletteEntries : Nat)
    (pass : Adam7Pass) (passY passWidth passX : Nat)
    (hpassX : passX < passWidth)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hentries : paletteIndexLimit bitDepth ≤ paletteEntries)
    (hstep : 0 < pass.stepX)
    (hdst : ∀ x, x < passWidth →
      adam7PaletteDstIndex w pass passY x < flat.size) :
    ∃ out,
      adam7ScatterRowPalette row flat w bitDepth paletteEntries pass passY passWidth =
        some out ∧
      out.get! (adam7PaletteDstIndex w pass passY passX) =
        palettePackedIndexAt row bitDepth passX := by
  rcases
    adam7ScatterRowPaletteLoop_get!_of_indexLimit row flat w bitDepth paletteEntries pass
      passY 0 passWidth passX hbd hentries hstep hdst with
    ⟨out, hout, hget⟩
  refine ⟨out, ?_, ?_⟩
  · simpa [adam7ScatterRowPalette] using hout
  · simpa [hpassX] using hget

private lemma packedZeroNat1 (row : ByteArray) (x : Nat)
    (hzero : palettePackedIndexAt row 1 x = 0) :
    ((row.get! (x / 8)).toNat >>> (7 - x % 8)) % 2 = 0 := by
  have hz :
      u8 (((row.get! (x / 8)).toNat >>> (7 - x % 8)) % 2) = 0 := by
    simpa [palettePackedIndexAt, palettePackedShift, paletteIndexLimit] using hzero
  have hzNat := congrArg UInt8.toNat hz
  have hlt : ((row.get! (x / 8)).toNat >>> (7 - x % 8)) % 2 < 256 := by
    have hmod :
        ((row.get! (x / 8)).toNat >>> (7 - x % 8)) % 2 < 2 :=
      Nat.mod_lt _ (by decide : 0 < 2)
    omega
  simpa [u8_toNat_of_lt _ hlt] using hzNat

private lemma packedZeroNat2 (row : ByteArray) (x : Nat)
    (hzero : palettePackedIndexAt row 2 x = 0) :
    ((row.get! (x / 4)).toNat >>> (6 - 2 * (x % 4))) % 4 = 0 := by
  have hz :
      u8 (((row.get! (x / 4)).toNat >>> (6 - 2 * (x % 4))) % 4) = 0 := by
    simpa [palettePackedIndexAt, palettePackedShift, paletteIndexLimit] using hzero
  have hzNat := congrArg UInt8.toNat hz
  have hlt : ((row.get! (x / 4)).toNat >>> (6 - 2 * (x % 4))) % 4 < 256 := by
    have hmod :
        ((row.get! (x / 4)).toNat >>> (6 - 2 * (x % 4))) % 4 < 4 :=
      Nat.mod_lt _ (by decide : 0 < 4)
    omega
  simpa [u8_toNat_of_lt _ hlt] using hzNat

private lemma packedZeroNat4 (row : ByteArray) (x : Nat)
    (hzero : palettePackedIndexAt row 4 x = 0) :
    ((row.get! (x / 2)).toNat >>> (4 - 4 * (x % 2))) % 16 = 0 := by
  have hz :
      u8 (((row.get! (x / 2)).toNat >>> (4 - 4 * (x % 2))) % 16) = 0 := by
    simpa [palettePackedIndexAt, palettePackedShift, paletteIndexLimit] using hzero
  have hzNat := congrArg UInt8.toNat hz
  have hlt : ((row.get! (x / 2)).toNat >>> (4 - 4 * (x % 2))) % 16 < 256 := by
    have hmod :
        ((row.get! (x / 2)).toNat >>> (4 - 4 * (x % 2))) % 16 < 16 :=
      Nat.mod_lt _ (by decide : 0 < 16)
    omega
  simpa [u8_toNat_of_lt _ hlt] using hzNat

private lemma div_mod_ne_of_ne_of_div_eq (x y d : Nat) (_hpos : 0 < d)
    (hdiv : x / d = y / d) (hne : x ≠ y) :
    x % d ≠ y % d := by
  intro hmod
  have hx := (Nat.div_add_mod x d).symm
  have hy := (Nat.div_add_mod y d).symm
  apply hne
  calc
    x = x / d * d + x % d := by simpa [Nat.mul_comm] using hx
    _ = y / d * d + y % d := by rw [hdiv, hmod]
    _ = y := by simpa [Nat.mul_comm] using hy.symm

/-- Reading the same packed palette position just written returns the written
index for every supported indexed bit depth. This is the single-sample inverse
used by packed indexed row round-trip proofs. -/
lemma palettePackedIndexAt_pack_same (row : ByteArray) (bitDepth x : Nat) (idx : UInt8)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hidx : idx.toNat < paletteIndexLimit bitDepth)
    (hbyte : x / (8 / bitDepth) < row.size)
    (hzero : palettePackedIndexAt row bitDepth x = 0) :
    palettePackedIndexAt (palettePackIndexIntoRow row bitDepth x idx) bitDepth x = idx := by
  rcases hbd with rfl | rfl | rfl | rfl
  · have hbyte' : x / 8 < row.size := by simpa using hbyte
    have hidx' : idx.toNat < 2 := by simpa [paletteIndexLimit] using hidx
    have hz := packedZeroNat1 row x hzero
    unfold palettePackedIndexAt palettePackIndexIntoRow
    simp [palettePackedShift, paletteIndexLimit, byteArray_get!_set!_self _ _ _ hbyte']
    exact packedFieldWriteSame1 (row.get! (x / 8)) idx (x % 8)
      (Nat.mod_lt _ (by decide : 0 < 8)) hidx' hz
  · have hbyte' : x / 4 < row.size := by simpa using hbyte
    have hidx' : idx.toNat < 4 := by simpa [paletteIndexLimit] using hidx
    have hz := packedZeroNat2 row x hzero
    unfold palettePackedIndexAt palettePackIndexIntoRow
    simp [palettePackedShift, paletteIndexLimit, byteArray_get!_set!_self _ _ _ hbyte']
    exact packedFieldWriteSame2 (row.get! (x / 4)) idx (x % 4)
      (Nat.mod_lt _ (by decide : 0 < 4)) hidx' hz
  · have hbyte' : x / 2 < row.size := by simpa using hbyte
    have hidx' : idx.toNat < 16 := by simpa [paletteIndexLimit] using hidx
    have hz := packedZeroNat4 row x hzero
    unfold palettePackedIndexAt palettePackIndexIntoRow
    simp [palettePackedShift, paletteIndexLimit, byteArray_get!_set!_self _ _ _ hbyte']
    exact packedFieldWriteSame4 (row.get! (x / 2)) idx (x % 2)
      (Nat.mod_lt _ (by decide : 0 < 2)) hidx' hz
  · have hbyte' : x < row.size := by simpa using hbyte
    unfold palettePackedIndexAt palettePackIndexIntoRow
    simp [byteArray_get!_set!_self _ _ _ hbyte']

/-- Packing one palette index does not change any other packed sample in the
row. This is the non-overlap fact needed by packed row induction and Adam7
scatter proofs. -/
lemma palettePackedIndexAt_pack_other (row : ByteArray) (bitDepth x y : Nat) (idx : UInt8)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hbyte : x / (8 / bitDepth) < row.size)
    (hne : x ≠ y) :
    palettePackedIndexAt (palettePackIndexIntoRow row bitDepth x idx) bitDepth y =
      palettePackedIndexAt row bitDepth y := by
  rcases hbd with rfl | rfl | rfl | rfl
  · have hxbyte : x / 8 < row.size := by simpa using hbyte
    unfold palettePackedIndexAt palettePackIndexIntoRow
    by_cases hsame : x / 8 = y / 8
    · have hmodne : x % 8 ≠ y % 8 :=
        div_mod_ne_of_ne_of_div_eq x y 8 (by decide) hsame hne
      rw [← hsame]
      simp [palettePackedShift, paletteIndexLimit,
        byteArray_get!_set!_self _ _ _ hxbyte]
      exact packedFieldWriteOther1 (row.get! (x / 8)) idx (x % 8) (y % 8)
        (Nat.mod_lt _ (by decide : 0 < 8)) (Nat.mod_lt _ (by decide : 0 < 8)) hmodne
    · simp [palettePackedShift, paletteIndexLimit,
        byteArray_get!_set!_ne _ _ _ _ hsame]
  · have hxbyte : x / 4 < row.size := by simpa using hbyte
    unfold palettePackedIndexAt palettePackIndexIntoRow
    by_cases hsame : x / 4 = y / 4
    · have hmodne : x % 4 ≠ y % 4 :=
        div_mod_ne_of_ne_of_div_eq x y 4 (by decide) hsame hne
      rw [← hsame]
      simp [palettePackedShift, paletteIndexLimit,
        byteArray_get!_set!_self _ _ _ hxbyte]
      exact packedFieldWriteOther2 (row.get! (x / 4)) idx (x % 4) (y % 4)
        (Nat.mod_lt _ (by decide : 0 < 4)) (Nat.mod_lt _ (by decide : 0 < 4)) hmodne
    · simp [palettePackedShift, paletteIndexLimit,
        byteArray_get!_set!_ne _ _ _ _ hsame]
  · have hxbyte : x / 2 < row.size := by simpa using hbyte
    unfold palettePackedIndexAt palettePackIndexIntoRow
    by_cases hsame : x / 2 = y / 2
    · have hmodne : x % 2 ≠ y % 2 :=
        div_mod_ne_of_ne_of_div_eq x y 2 (by decide) hsame hne
      rw [← hsame]
      simp [palettePackedShift, paletteIndexLimit,
        byteArray_get!_set!_self _ _ _ hxbyte]
      exact packedFieldWriteOther4 (row.get! (x / 2)) idx (x % 2) (y % 2)
        (Nat.mod_lt _ (by decide : 0 < 2)) (Nat.mod_lt _ (by decide : 0 < 2)) hmodne
    · simp [palettePackedShift, paletteIndexLimit,
        byteArray_get!_set!_ne _ _ _ _ hsame]
  · unfold palettePackedIndexAt palettePackIndexIntoRow
    simp [byteArray_get!_set!_ne _ _ _ _ hne]

private lemma palettePackIndexIntoRow_size_core
    (row : ByteArray) (bitDepth x : Nat) (idx : UInt8) :
    (palettePackIndexIntoRow row bitDepth x idx).size = row.size := by
  unfold palettePackIndexIntoRow
  by_cases h8 : bitDepth == 8
  · rw [if_pos h8]
    exact byteArray_size_set! row x idx
  · rw [if_neg h8]
    exact byteArray_size_set! row (x / (8 / bitDepth))
        (u8 ((row.get! (x / (8 / bitDepth))).toNat |||
          (idx.toNat % paletteIndexLimit bitDepth) <<< palettePackedShift bitDepth x))

/-- The byte containing a supported packed palette sample lies inside the
allocated packed row. This is the bounds bridge from image width to row bytes. -/
lemma palettePackedByteIndex_lt_rowBytes (w bitDepth x : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8)
    (hx : x < w) :
    x / (8 / bitDepth) < paletteRowBytes w bitDepth := by
  rcases hbd with rfl | rfl | rfl | rfl
  · rw [paletteRowBytes_1]
    change x / 8 < (w + 7) / 8
    apply Nat.div_lt_of_lt_mul
    have hceil : w ≤ ((w + 7) / 8) * 8 := by omega
    exact Nat.lt_of_lt_of_le hx (by simpa [Nat.mul_comm] using hceil)
  · rw [paletteRowBytes_2]
    change x / 4 < (w + 3) / 4
    apply Nat.div_lt_of_lt_mul
    have hceil : w ≤ ((w + 3) / 4) * 4 := by omega
    exact Nat.lt_of_lt_of_le hx (by simpa [Nat.mul_comm] using hceil)
  · rw [paletteRowBytes_4]
    change x / 2 < (w + 1) / 2
    apply Nat.div_lt_of_lt_mul
    have hceil : w ≤ ((w + 1) / 2) * 2 := by omega
    exact Nat.lt_of_lt_of_le hx (by simpa [Nat.mul_comm] using hceil)
  · rw [paletteRowBytes_8]
    simpa using hx

private lemma palettePackedIndexAt_zeroRow (rowBytes bitDepth x : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4 ∨ bitDepth = 8) :
    palettePackedIndexAt (ByteArray.mk <| Array.replicate rowBytes 0) bitDepth x = 0 := by
  rcases hbd with rfl | rfl | rfl | rfl <;>
    simp [palettePackedIndexAt, palettePackedShift, paletteIndexLimit,
      byteArray_get!_replicate_zero, u8]

/-- Packing the remaining indices of one row preserves already-written samples,
writes every later sample, and leaves no source index changed. This is the
row-local arbitrary-width inverse for supported packed palette bit depths. -/
lemma encodeIndexedPackedRowLoop_indices
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (rowBytes y x : Nat) (row : ByteArray)
    (hrowBytes : rowBytes = paletteRowBytes bmp.size.width bmp.bitDepth)
    (hrow : row.size = rowBytes)
    (hrange :
      ∀ z, z < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + z)).toNat < paletteIndexLimit bmp.bitDepth)
    (hprefix :
      ∀ z, z < bmp.size.width → z < x →
        palettePackedIndexAt row bmp.bitDepth z =
          bmp.data.get! (y * bmp.size.width + z))
    (hzero :
      ∀ z, z < bmp.size.width → x ≤ z →
        palettePackedIndexAt row bmp.bitDepth z = 0) :
    ∀ z, z < bmp.size.width →
      palettePackedIndexAt (encodeIndexedPackedRowLoop bmp rowBytes y x row)
        bmp.bitDepth z = bmp.data.get! (y * bmp.size.width + z) := by
  have hk :
      ∀ k, ∀ x row,
        bmp.size.width - x = k →
        row.size = rowBytes →
        (∀ z, z < bmp.size.width → z < x →
          palettePackedIndexAt row bmp.bitDepth z =
            bmp.data.get! (y * bmp.size.width + z)) →
        (∀ z, z < bmp.size.width → x ≤ z →
          palettePackedIndexAt row bmp.bitDepth z = 0) →
        ∀ z, z < bmp.size.width →
          palettePackedIndexAt (encodeIndexedPackedRowLoop bmp rowBytes y x row)
            bmp.bitDepth z = bmp.data.get! (y * bmp.size.width + z) := by
    intro k
    induction k with
    | zero =>
        intro x row hk hrow hprefix hzero z hz
        have hxge : bmp.size.width ≤ x := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ x < bmp.size.width := not_lt_of_ge hxge
        have hzltx : z < x := Nat.lt_of_lt_of_le hz hxge
        simp [encodeIndexedPackedRowLoop, hlt, hprefix z hz hzltx]
    | succ k ih =>
        intro x row hk hrow hprefix hzero z hz
        have hlt : x < bmp.size.width := Nat.lt_of_sub_eq_succ hk
        let idx := bmp.data.get! (y * bmp.size.width + x)
        let row' := palettePackIndexIntoRow row bmp.bitDepth x idx
        have hbyte : x / (8 / bmp.bitDepth) < row.size := by
          rw [hrow, hrowBytes]
          exact palettePackedByteIndex_lt_rowBytes bmp.size.width bmp.bitDepth x hbd hlt
        have hsame :
            palettePackedIndexAt row' bmp.bitDepth x = idx := by
          simpa [row'] using
            palettePackedIndexAt_pack_same row bmp.bitDepth x idx hbd (hrange x hlt)
              hbyte (hzero x hlt le_rfl)
        have hrow' : row'.size = rowBytes := by
          simpa [row'] using
            (palettePackIndexIntoRow_size_core row bmp.bitDepth x idx).trans hrow
        have hprefix' :
            ∀ z, z < bmp.size.width → z < x + 1 →
              palettePackedIndexAt row' bmp.bitDepth z =
                bmp.data.get! (y * bmp.size.width + z) := by
          intro z hz hzlt
          by_cases hzx : z = x
          · subst z
            simpa [idx] using hsame
          · have hzltx : z < x := by omega
            have hother :
                palettePackedIndexAt row' bmp.bitDepth z =
                  palettePackedIndexAt row bmp.bitDepth z := by
              simpa [row'] using
                palettePackedIndexAt_pack_other row bmp.bitDepth x z idx hbd hbyte
                  (by exact fun h => hzx h.symm)
            exact hother.trans (hprefix z hz hzltx)
        have hzero' :
            ∀ z, z < bmp.size.width → x + 1 ≤ z →
              palettePackedIndexAt row' bmp.bitDepth z = 0 := by
          intro z hz hxz
          have hne : x ≠ z := by omega
          have hother :
              palettePackedIndexAt row' bmp.bitDepth z =
                palettePackedIndexAt row bmp.bitDepth z := by
            simpa [row'] using
              palettePackedIndexAt_pack_other row bmp.bitDepth x z idx hbd hbyte hne
          exact hother.trans (hzero z hz (by omega))
        have hk' : bmp.size.width - (x + 1) = k := by
          have hsum : bmp.size.width = Nat.succ k + x :=
            Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            bmp.size.width - (x + 1) = (Nat.succ k + x) - (x + 1) := by simp [hsum]
            _ = k := by omega
        have hnext :=
          ih (x := x + 1) (row := row') hk' hrow' hprefix' hzero' z hz
        have hdef :=
          congrArg (fun f => palettePackedIndexAt f bmp.bitDepth z)
            (encodeIndexedPackedRowLoop.eq_1
              (bmp := bmp) (rowBytes := rowBytes) (y := y) (x := x) (row := row))
        calc
          palettePackedIndexAt (encodeIndexedPackedRowLoop bmp rowBytes y x row)
              bmp.bitDepth z =
            palettePackedIndexAt
              (if x < bmp.size.width then
                encodeIndexedPackedRowLoop bmp rowBytes y (x + 1) row'
               else row) bmp.bitDepth z := by
                simpa [row'] using hdef
          _ = palettePackedIndexAt
              (encodeIndexedPackedRowLoop bmp rowBytes y (x + 1) row')
              bmp.bitDepth z := by simp [hlt]
          _ = bmp.data.get! (y * bmp.size.width + z) := hnext
  exact hk (bmp.size.width - x) x row rfl hrow hprefix hzero

/-- Starting from a zero row, packing one indexed source row round-trips through
`palettePackedIndexAt` at every column for every supported palette bit depth. -/
lemma encodeIndexedPackedRowLoop_zeroRow_indices
    (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (y : Nat)
    (hrange :
      ∀ z, z < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + z)).toNat < paletteIndexLimit bmp.bitDepth) :
    let rowBytes := paletteRowBytes bmp.size.width bmp.bitDepth
    let row0 := ByteArray.mk <| Array.replicate rowBytes 0
    ∀ z, z < bmp.size.width →
      palettePackedIndexAt (encodeIndexedPackedRowLoop bmp rowBytes y 0 row0)
        bmp.bitDepth z = bmp.data.get! (y * bmp.size.width + z) := by
  intro rowBytes row0
  have hrow : row0.size = rowBytes := by
    simp [row0, ByteArray.size, Array.size_replicate]
  exact
    encodeIndexedPackedRowLoop_indices
      (bmp := bmp) hbd (rowBytes := rowBytes) (y := y) (x := 0) (row := row0)
      (by rfl) hrow hrange
      (by intro z _ hzlt; omega)
      (by
        intro z hz _
        exact palettePackedIndexAt_zeroRow rowBytes bmp.bitDepth z hbd)

private lemma u8_mul257_div256_eq_self (sample : UInt8) :
    u8 (sample.toNat * 257 / 256) = sample := by
  have hs : sample.toNat < 256 := by
    simpa using UInt8.toNat_lt sample
  have hdiv : sample.toNat * 257 / 256 = sample.toNat := by
    rw [show sample.toNat * 257 = sample.toNat + 256 * sample.toNat by omega]
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256)]
    rw [Nat.div_eq_of_lt hs]
    omega
  rw [hdiv]
  exact UInt8.toNat.inj (u8_toNat_of_lt sample.toNat hs)

private lemma u8_mul257_eq_self (sample : UInt8) :
    u8 (sample.toNat * 257) = sample := by
  have hs : sample.toNat < 256 := by
    simpa using UInt8.toNat_lt sample
  change UInt8.ofNat (sample.toNat * 257) = sample
  rw [UInt8.ofNat_eq_iff_mod_eq_toNat]
  rw [show sample.toNat * 257 = 256 * sample.toNat + sample.toNat by omega]
  change (256 * sample.toNat + sample.toNat) % 256 = sample.toNat
  rw [Nat.add_comm]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]

/-- Full-range 16-bit palette expansion writes an 8-bit sample as duplicated
big-endian bytes. This pins the `u8 * 257` channel expansion rule. -/
lemma pushU16Full_eq_push_sample_twice (out : ByteArray) (sample : UInt8) :
    pushU16Full out sample = (out.push sample).push sample := by
  unfold pushU16Full pushU16BE
  rw [u8_mul257_div256_eq_self, u8_mul257_eq_self]

/-- Alpha compositing with a fully opaque palette alpha returns the palette
sample. This pins the `tRNS` alpha endpoint used with `bKGD` compositing. -/
lemma alphaCompositeByte_opaque (src bg : UInt8) :
    alphaCompositeByte src bg 0xff = src := by
  unfold alphaCompositeByte
  have h255 : (0xff : UInt8).toNat = 255 := by decide
  simp [h255]
  exact u8_toNat_eq_self src

/-- Alpha compositing with a fully transparent palette alpha returns the
background sample. This pins the transparent `tRNS` endpoint over `bKGD`. -/
lemma alphaCompositeByte_transparent (src bg : UInt8) :
    alphaCompositeByte src bg 0 = bg := by
  unfold alphaCompositeByte
  have h0 : (0 : UInt8).toNat = 0 := by decide
  simp [h0]
  exact u8_toNat_eq_self bg

/-- Alpha compositing a sample over the same background sample is idempotent
for every alpha value. This is a palette compositing stability fact. -/
lemma alphaCompositeByte_same (sample alpha : UInt8) :
    alphaCompositeByte sample sample alpha = sample := by
  unfold alphaCompositeByte
  have ha : alpha.toNat ≤ 255 := by
    have hlt : alpha.toNat < 256 := by
      simpa using UInt8.toNat_lt alpha
    omega
  have hnum :
      sample.toNat * alpha.toNat + sample.toNat * (255 - alpha.toNat) =
        sample.toNat * 255 := by
    rw [← Nat.mul_add]
    have hsum : alpha.toNat + (255 - alpha.toNat) = 255 := by
      omega
    rw [hsum]
  rw [hnum]
  have hdiv : sample.toNat * 255 / 255 = sample.toNat := by
    rw [Nat.mul_comm sample.toNat 255]
    exact Nat.mul_div_right sample.toNat (by decide : 0 < 255)
  rw [hdiv]
  exact u8_toNat_eq_self sample

/-- Converting a palette entry whose RGB channels are equal to grayscale keeps
that sample unchanged. This is the grayscale-target palette expansion base fact. -/
lemma grayFromRGB8_uniform (sample : UInt8) :
    grayFromRGB8 sample sample sample = sample := by
  unfold grayFromRGB8
  have hdiv : (sample.toNat + sample.toNat + sample.toNat) / 3 = sample.toNat := by
    rw [show sample.toNat + sample.toNat + sample.toNat = sample.toNat * 3 by omega]
    rw [Nat.mul_comm sample.toNat 3]
    exact Nat.mul_div_right sample.toNat (by decide : 0 < 3)
  rw [hdiv]
  exact u8_toNat_eq_self sample

/-- Full-range 16-bit grayscale expansion of a uniform RGB palette entry writes
the duplicated sample bytes. This combines gray conversion with `u8 * 257`. -/
lemma pushU16Full_grayFromRGB8_uniform (out : ByteArray) (sample : UInt8) :
    pushU16Full out (grayFromRGB8 sample sample sample) =
      (out.push sample).push sample := by
  rw [grayFromRGB8_uniform, pushU16Full_eq_push_sample_twice]

/-- Palette transparency metadata exposes its alpha byte payload unchanged.
This pins the handoff from parsed `tRNS` metadata into palette expansion. -/
@[simp] lemma paletteAlphaBytes?_paletteAlpha (alpha : ByteArray) :
    paletteAlphaBytes? { PngMetadata.empty with transparency := some (.paletteAlpha alpha) } =
      some alpha := by
  simp [paletteAlphaBytes?]

/-- Without palette transparency metadata, no palette alpha byte payload is
available. This is the default branch consumed by palette expansion. -/
@[simp] lemma paletteAlphaBytes?_none :
    paletteAlphaBytes? PngMetadata.empty = none := by
  simp [paletteAlphaBytes?, PngMetadata.empty]

/-- Non-palette transparency metadata is ignored by the palette-alpha helper.
This separates indexed `tRNS` handling from gray/RGB transparency metadata. -/
lemma paletteAlphaBytes?_non_palette (trns : PngTransparency)
    (h : ∀ alpha, trns ≠ .paletteAlpha alpha) :
    paletteAlphaBytes? { PngMetadata.empty with transparency := some trns } = none := by
  cases trns <;> simp [paletteAlphaBytes?] at h ⊢

/-- Without palette `tRNS`, every palette entry is treated as fully opaque.
This records the decoder's default-alpha rule for indexed PNGs. -/
@[simp] lemma paletteAlphaAt_none (idx : Nat) :
    paletteAlphaAt none idx = 0xff := by
  rfl

/-- The default palette alpha behaves as fully opaque under compositing. This
connects missing palette `tRNS` metadata to the compositing endpoint. -/
lemma alphaCompositeByte_paletteAlphaAt_none (src bg : UInt8) (idx : Nat) :
    alphaCompositeByte src bg (paletteAlphaAt none idx) = src := by
  simpa using alphaCompositeByte_opaque src bg

/-- Palette alpha bytes are read directly when the index is inside the `tRNS`
payload. This is the in-range branch used by palette RGBA expansion. -/
lemma paletteAlphaAt_some_lt (alpha : ByteArray) (idx : Nat) (hidx : idx < alpha.size) :
    paletteAlphaAt (some alpha) idx = alpha.get! idx := by
  unfold paletteAlphaAt
  simp [hidx]

/-- Palette entries beyond the provided `tRNS` payload default to fully opaque.
This is PNG's partial-palette-alpha behavior. -/
lemma paletteAlphaAt_some_ge (alpha : ByteArray) (idx : Nat) (hidx : alpha.size ≤ idx) :
    paletteAlphaAt (some alpha) idx = 0xff := by
  unfold paletteAlphaAt
  simp [Nat.not_lt_of_ge hidx]

/-- Palette background metadata is resolved by looking up the named palette
entry in `PLTE`. This pins the `bKGD` handoff used by non-alpha targets. -/
lemma paletteBackgroundRGB?_paletteIndex (palette : PngPalette) (idx : UInt8) :
    paletteBackgroundRGB? palette
      { PngMetadata.empty with background := some (.paletteIndex idx) } =
        palette.rgbAt? idx.toNat := by
  simp [paletteBackgroundRGB?]

/-- Without palette background metadata, the palette background helper returns
no RGB value. This is the default branch for indexed `bKGD` compositing. -/
@[simp] lemma paletteBackgroundRGB?_none (palette : PngPalette) :
    paletteBackgroundRGB? palette PngMetadata.empty = none := by
  simp [paletteBackgroundRGB?, PngMetadata.empty]

/-- Non-palette background metadata is ignored by the palette background helper.
This separates indexed `bKGD` lookup from gray/RGB background metadata. -/
lemma paletteBackgroundRGB?_non_palette (palette : PngPalette) (background : PngBackground)
    (h : ∀ idx, background ≠ .paletteIndex idx) :
    paletteBackgroundRGB? palette
      { PngMetadata.empty with background := some background } = none := by
  cases background <;> simp [paletteBackgroundRGB?] at h ⊢

/-- A palette lookup succeeds when the requested RGB triplet is inside `PLTE`.
This exposes the exact bytes selected by a valid indexed-color sample. -/
lemma paletteRgbAt?_of_base_lt (palette : PngPalette) (idx : Nat)
    (h : idx * 3 + 2 < palette.entries.size) :
    palette.rgbAt? idx =
      some (palette.entries.get! (idx * 3),
        palette.entries.get! (idx * 3 + 1),
        palette.entries.get! (idx * 3 + 2)) := by
  unfold PngPalette.rgbAt?
  simp [h]

/-- A palette lookup fails when the requested RGB triplet is outside `PLTE`.
This is the out-of-range branch used by palette expansion rejection proofs. -/
lemma paletteRgbAt?_of_base_ge (palette : PngPalette) (idx : Nat)
    (h : palette.entries.size ≤ idx * 3 + 2) :
    palette.rgbAt? idx = none := by
  unfold PngPalette.rgbAt?
  simp [Nat.not_lt_of_ge h]

/-- For triplet-aligned palettes, every index below `entryCount` has a full RGB
triplet. This connects parser `PLTE` validation to successful palette lookup. -/
lemma paletteRgbAt?_of_lt_entryCount (palette : PngPalette) (idx : Nat)
    (htriplets : palette.entries.size % 3 = 0)
    (hidx : idx < palette.entryCount) :
    palette.rgbAt? idx =
      some (palette.entries.get! (idx * 3),
        palette.entries.get! (idx * 3 + 1),
        palette.entries.get! (idx * 3 + 2)) := by
  have hsizeMul : 3 * (palette.entries.size / 3) = palette.entries.size := by
    have hmod := Nat.mod_add_div palette.entries.size 3
    omega
  have hsize : palette.entries.size = palette.entryCount * 3 := by
    simpa [PngPalette.entryCount, Nat.mul_comm] using hsizeMul.symm
  have hidxSucc : idx + 1 ≤ palette.entryCount := Nat.succ_le_of_lt hidx
  have hmul : (idx + 1) * 3 ≤ palette.entryCount * 3 :=
    Nat.mul_le_mul_right 3 hidxSucc
  have hle : (idx + 1) * 3 ≤ palette.entries.size := by
    simpa [hsize] using hmul
  have hbase : idx * 3 + 2 < palette.entries.size := by
    have hstep : idx * 3 + 2 < (idx + 1) * 3 := by
      omega
    exact Nat.lt_of_lt_of_le hstep hle
  exact paletteRgbAt?_of_base_lt palette idx hbase

/-- A valid palette `bKGD` index resolves to its `PLTE` triplet. This links
metadata validation to the background color used for compositing. -/
lemma paletteBackgroundRGB?_paletteIndex_of_lt_entryCount
    (palette : PngPalette) (idx : UInt8)
    (htriplets : palette.entries.size % 3 = 0)
    (hidx : idx.toNat < palette.entryCount) :
    paletteBackgroundRGB? palette
      { PngMetadata.empty with background := some (.paletteIndex idx) } =
        some (palette.entries.get! (idx.toNat * 3),
          palette.entries.get! (idx.toNat * 3 + 1),
          palette.entries.get! (idx.toNat * 3 + 2)) := by
  rw [paletteBackgroundRGB?_paletteIndex]
  exact paletteRgbAt?_of_lt_entryCount palette idx.toNat htriplets hidx

/-- Palette expansion to 8-bit samples rejects target color types outside the
supported grayscale/RGB/gray-alpha/RGBA set. -/
lemma expandPaletteIndicesToPixels8_unsupported_colorType
    (indices : ByteArray) (palette : PngPalette)
    (alpha? : Option ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8)
    (h0 : targetColorType ≠ u8 0)
    (h2 : targetColorType ≠ u8 2)
    (h4 : targetColorType ≠ u8 4)
    (h6 : targetColorType ≠ u8 6) :
    expandPaletteIndicesToPixels8 indices palette alpha? background? targetColorType = none := by
  unfold expandPaletteIndicesToPixels8
  simp [h0, h2, h4, h6]
  rfl

/-- Palette expansion to 16-bit samples rejects target color types outside the
supported grayscale/RGB/gray-alpha/RGBA set. -/
lemma expandPaletteIndicesToPixels16_unsupported_colorType
    (indices : ByteArray) (palette : PngPalette)
    (alpha? : Option ByteArray) (background? : Option (UInt8 × UInt8 × UInt8))
    (targetColorType : UInt8)
    (h0 : targetColorType ≠ u8 0)
    (h2 : targetColorType ≠ u8 2)
    (h4 : targetColorType ≠ u8 4)
    (h6 : targetColorType ≠ u8 6) :
    expandPaletteIndicesToPixels16 indices palette alpha? background? targetColorType = none := by
  unfold expandPaletteIndicesToPixels16
  simp [h0, h2, h4, h6]
  rfl

/-- Expanding an empty palette index buffer to any supported 8-bit target
produces an empty pixel buffer. This is the palette expansion loop base case. -/
lemma expandPaletteIndicesToPixels8_empty_supported
    (palette : PngPalette) (alpha? : Option ByteArray)
    (background? : Option (UInt8 × UInt8 × UInt8)) (targetColorType : UInt8)
    (hct : targetColorType = u8 0 ∨ targetColorType = u8 2 ∨
      targetColorType = u8 4 ∨ targetColorType = u8 6) :
    expandPaletteIndicesToPixels8 ByteArray.empty palette alpha? background?
      targetColorType = some ByteArray.empty := by
  rcases hct with rfl | rfl | rfl | rfl
  all_goals
    unfold expandPaletteIndicesToPixels8
    simp [Std.Legacy.Range.forIn_eq_forIn_range']
    rfl

/-- Expanding an empty palette index buffer to any supported 16-bit target
produces an empty pixel buffer. This pins the 16-bit expansion loop base case. -/
lemma expandPaletteIndicesToPixels16_empty_supported
    (palette : PngPalette) (alpha? : Option ByteArray)
    (background? : Option (UInt8 × UInt8 × UInt8)) (targetColorType : UInt8)
    (hct : targetColorType = u8 0 ∨ targetColorType = u8 2 ∨
      targetColorType = u8 4 ∨ targetColorType = u8 6) :
    expandPaletteIndicesToPixels16 ByteArray.empty palette alpha? background?
      targetColorType = some ByteArray.empty := by
  rcases hct with rfl | rfl | rfl | rfl
  all_goals
    unfold expandPaletteIndicesToPixels16
    simp [Std.Legacy.Range.forIn_eq_forIn_range']
    rfl

/-- The public palette expansion wrapper returns an empty pixel buffer for an
empty index buffer whenever both target color type and bit depth are supported. -/
lemma expandPaletteIndicesToPixels_empty_supported
    (palette : PngPalette) (metadata : PngMetadata)
    (targetColorType targetBitDepth : UInt8)
    (hct : targetColorType = u8 0 ∨ targetColorType = u8 2 ∨
      targetColorType = u8 4 ∨ targetColorType = u8 6)
    (hbd : targetBitDepth = u8 8 ∨ targetBitDepth = u8 16) :
    expandPaletteIndicesToPixels ByteArray.empty palette metadata targetColorType
      targetBitDepth = some ByteArray.empty := by
  rcases hbd with rfl | rfl
  · simpa [expandPaletteIndicesToPixels] using
      expandPaletteIndicesToPixels8_empty_supported palette
        (paletteAlphaBytes? metadata) (paletteBackgroundRGB? palette metadata)
        targetColorType hct
  · have hne : (u8 16 : UInt8) ≠ u8 8 := by decide
    simpa [expandPaletteIndicesToPixels, hne] using
      expandPaletteIndicesToPixels16_empty_supported palette
        (paletteAlphaBytes? metadata) (paletteBackgroundRGB? palette metadata)
        targetColorType hct

/-- The public palette expansion wrapper rejects unsupported target color types
when the requested target bit depth is otherwise supported. -/
lemma expandPaletteIndicesToPixels_unsupported_colorType
    (indices : ByteArray) (palette : PngPalette) (metadata : PngMetadata)
    (targetColorType targetBitDepth : UInt8)
    (h0 : targetColorType ≠ u8 0)
    (h2 : targetColorType ≠ u8 2)
    (h4 : targetColorType ≠ u8 4)
    (h6 : targetColorType ≠ u8 6)
    (hbd : targetBitDepth = u8 8 ∨ targetBitDepth = u8 16) :
    expandPaletteIndicesToPixels indices palette metadata targetColorType
      targetBitDepth = none := by
  rcases hbd with rfl | rfl
  · simpa [expandPaletteIndicesToPixels] using
      expandPaletteIndicesToPixels8_unsupported_colorType indices palette
        (paletteAlphaBytes? metadata) (paletteBackgroundRGB? palette metadata)
        targetColorType h0 h2 h4 h6
  · have hne : (u8 16 : UInt8) ≠ u8 8 := by decide
    simpa [expandPaletteIndicesToPixels, hne] using
      expandPaletteIndicesToPixels16_unsupported_colorType indices palette
        (paletteAlphaBytes? metadata) (paletteBackgroundRGB? palette metadata)
        targetColorType h0 h2 h4 h6

/-- Palette expansion rejects target bit depths other than 8 or 16. This pins
the public expansion wrapper's bit-depth boundary. -/
lemma expandPaletteIndicesToPixels_unsupported_bitDepth
    (indices : ByteArray) (palette : PngPalette) (metadata : PngMetadata)
    (targetColorType targetBitDepth : UInt8)
    (h8 : targetBitDepth ≠ u8 8)
    (h16 : targetBitDepth ≠ u8 16) :
    expandPaletteIndicesToPixels indices palette metadata targetColorType targetBitDepth = none := by
  unfold expandPaletteIndicesToPixels
  simp [h8, h16]

/-- Packing one indexed sample into a row does not change the row byte count.
This is the inner-loop invariant for indexed row construction. -/
lemma palettePackIndexIntoRow_size (row : ByteArray) (bitDepth x : Nat) (idx : UInt8) :
    (palettePackIndexIntoRow row bitDepth x idx).size = row.size := by
  unfold palettePackIndexIntoRow
  by_cases h8 : bitDepth == 8
  · rw [if_pos h8]
    exact byteArray_size_set! row x idx
  · rw [if_neg h8]
    exact byteArray_size_set! row (x / (8 / bitDepth))
        (u8 ((row.get! (x / (8 / bitDepth))).toNat |||
          (idx.toNat % paletteIndexLimit bitDepth) <<< palettePackedShift bitDepth x))

/-- Writing all indices for one packed row preserves the allocated row size.
This proves the inner indexed row encoder cannot grow or shrink rows. -/
lemma encodeIndexedPackedRowLoop_size (bmp : PngIndexedBitmap)
    (rowBytes y x : Nat) (row : ByteArray) (hrow : row.size = rowBytes) :
    (encodeIndexedPackedRowLoop bmp rowBytes y x row).size = rowBytes := by
  have hk :
      ∀ k, ∀ x row,
        bmp.size.width - x = k → row.size = rowBytes →
        (encodeIndexedPackedRowLoop bmp rowBytes y x row).size = rowBytes := by
    intro k
    induction k with
    | zero =>
        intro x row hk hrow
        have hx : bmp.size.width ≤ x := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ x < bmp.size.width := not_lt_of_ge hx
        simp [encodeIndexedPackedRowLoop, hlt, hrow]
    | succ k ih =>
        intro x row hk hrow
        have hlt : x < bmp.size.width := Nat.lt_of_sub_eq_succ hk
        let row' := palettePackIndexIntoRow row bmp.bitDepth x
          (bmp.data.get! (y * bmp.size.width + x))
        have hrow' : row'.size = rowBytes := by
          simpa [row'] using
            palettePackIndexIntoRow_size row bmp.bitDepth x
              (bmp.data.get! (y * bmp.size.width + x)) |>.trans hrow
        have hk' : bmp.size.width - (x + 1) = k := by
          have hsum : bmp.size.width = Nat.succ k + x :=
            Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            bmp.size.width - (x + 1) = (Nat.succ k + x) - (x + 1) := by simp [hsum]
            _ = k := by omega
        have ih' := ih (x := x + 1) (row := row') hk' hrow'
        have hdef :=
          congrArg ByteArray.size
            (encodeIndexedPackedRowLoop.eq_1
              (bmp := bmp) (rowBytes := rowBytes) (y := y) (x := x) (row := row))
        calc
          (encodeIndexedPackedRowLoop bmp rowBytes y x row).size =
              (if x < bmp.size.width then
                encodeIndexedPackedRowLoop bmp rowBytes y (x + 1) row'
               else row).size := by
                simpa [row'] using hdef
          _ = (encodeIndexedPackedRowLoop bmp rowBytes y (x + 1) row').size := by
                simp [hlt]
          _ = rowBytes := ih'
  exact hk (bmp.size.width - x) x row rfl hrow

/-- Appending every packed indexed row yields height times packed row bytes.
This is the storage-size invariant for the indexed row packer. -/
lemma encodeIndexedPackedRowsLoop_size (bmp : PngIndexedBitmap)
    (rowBytes y : Nat) (packed : ByteArray)
    (hy : y ≤ bmp.size.height) (hpacked : packed.size = y * rowBytes) :
    (encodeIndexedPackedRowsLoop bmp rowBytes y packed).size =
      bmp.size.height * rowBytes := by
  have hk :
      ∀ k, ∀ y packed,
        bmp.size.height - y = k → y ≤ bmp.size.height →
        packed.size = y * rowBytes →
        (encodeIndexedPackedRowsLoop bmp rowBytes y packed).size =
          bmp.size.height * rowBytes := by
    intro k
    induction k with
    | zero =>
        intro y packed hk hy hpacked
        have hge : bmp.size.height ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < bmp.size.height := not_lt_of_ge hge
        have hyEq : y = bmp.size.height := Nat.le_antisymm hy hge
        simp [encodeIndexedPackedRowsLoop, hpacked, hyEq]
    | succ k ih =>
        intro y packed hk hy hpacked
        have hlt : y < bmp.size.height := Nat.lt_of_sub_eq_succ hk
        have hy' : y + 1 ≤ bmp.size.height := Nat.succ_le_of_lt hlt
        let row0 := ByteArray.mk <| Array.replicate rowBytes 0
        let row := encodeIndexedPackedRowLoop bmp rowBytes y 0 row0
        let packed' := packed ++ row
        have hrow0 : row0.size = rowBytes := by
          simp [row0, ByteArray.size, Array.size_replicate]
        have hrow : row.size = rowBytes := by
          simpa [row] using encodeIndexedPackedRowLoop_size bmp rowBytes y 0 row0 hrow0
        have hpacked' : packed'.size = (y + 1) * rowBytes := by
          calc
            packed'.size = packed.size + row.size := by
              simp [packed', ByteArray.size_append]
            _ = y * rowBytes + rowBytes := by
              simp [hpacked, hrow]
            _ = (y + 1) * rowBytes := by
              simp [Nat.add_mul, Nat.one_mul]
        have hk' : bmp.size.height - (y + 1) = k := by
          have hsum : bmp.size.height = Nat.succ k + y :=
            Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            bmp.size.height - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have ih' := ih (y := y + 1) (packed := packed') hk' hy' hpacked'
        have hdef :=
          congrArg ByteArray.size
            (encodeIndexedPackedRowsLoop.eq_1
              (bmp := bmp) (rowBytes := rowBytes) (y := y) (packed := packed))
        calc
          (encodeIndexedPackedRowsLoop bmp rowBytes y packed).size =
              (if y < bmp.size.height then
                encodeIndexedPackedRowsLoop bmp rowBytes (y + 1) packed'
               else packed).size := by
                simpa [row0, row, packed'] using hdef
          _ = (encodeIndexedPackedRowsLoop bmp rowBytes (y + 1) packed').size := by
                simp [hlt]
          _ = bmp.size.height * rowBytes := ih'
  exact hk (bmp.size.height - y) y packed rfl hy hpacked

/-- Packed indexed rows occupy exactly height times packed row bytes.
This is the packed-payload size fact used by raw indexed encoding. -/
lemma encodeIndexedPackedRows_size (bmp : PngIndexedBitmap) :
    (encodeIndexedPackedRows bmp).size =
      bmp.size.height * paletteRowBytes bmp.size.width bmp.bitDepth := by
  let rowBytes := paletteRowBytes bmp.size.width bmp.bitDepth
  unfold encodeIndexedPackedRows
  by_cases hbd : bmp.bitDepth = 8
  · have hrowBytes : rowBytes = bmp.size.width := by
      simpa [rowBytes, hbd] using paletteRowBytes_8 bmp.size.width
    calc
      (if bmp.bitDepth = 8 then bmp.data
        else encodeIndexedPackedRowsLoop bmp rowBytes 0 ByteArray.empty).size =
          bmp.data.size := by simp [hbd]
      _ = bmp.size.height * rowBytes := by
          calc
            bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
            _ = bmp.size.height * rowBytes := by
                simp [hrowBytes, Nat.mul_comm]
  · simpa [rowBytes, hbd] using
      encodeIndexedPackedRowsLoop_size (bmp := bmp) (rowBytes := rowBytes)
        (y := 0) (packed := ByteArray.empty) (Nat.zero_le _) (by simp)

/-- For 8-bit indexed bitmaps, packed rows are exactly the source index bytes.
This identity is the bridge from packed-row proofs back to `PngIndexedBitmap`. -/
lemma encodeIndexedPackedRows_8_eq_data (bmp : PngIndexedBitmap)
    (hbd : bmp.bitDepth = 8) :
    encodeIndexedPackedRows bmp = bmp.data := by
  unfold encodeIndexedPackedRows
  simp [hbd]

/-- Extracting one packed indexed row has the configured row size.
This is the local bound needed by raw indexed encoder size proofs. -/
lemma indexedPackedRow_extract_size (packedRows : ByteArray) (rowBytes h y : Nat)
    (hpacked : packedRows.size = h * rowBytes) (hy : y < h) :
    (packedRows.extract (y * rowBytes) (y * rowBytes + rowBytes)).size = rowBytes := by
  have hrow : y * rowBytes + rowBytes = (y + 1) * rowBytes := by
    simp [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hle : y * rowBytes + rowBytes ≤ packedRows.size := by
    have hy' : y + 1 ≤ h := Nat.succ_le_of_lt hy
    have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
      Nat.mul_le_mul_right rowBytes hy'
    simpa [hpacked, hrow] using hmul
  simp [ByteArray.size_extract, Nat.min_eq_left hle]

/-- Serialising packed indexed rows appends one filter byte plus one row per step.
This is the raw-size invariant for the recursive indexed row encoder. -/
lemma encodeIndexedRowsWithFilterLoop_size (packedRows : ByteArray)
    (rowBytes h y : Nat) (prev raw : ByteArray) (strategy : PngFilterStrategy)
    (hpacked : packedRows.size = h * rowBytes)
    (hy : y ≤ h)
    (hraw : raw.size = y * (rowBytes + 1)) :
    (encodeIndexedRowsWithFilterLoop packedRows rowBytes h y prev raw strategy).size =
      h * (rowBytes + 1) := by
  have hk :
      ∀ k, ∀ y prev raw,
        h - y = k → y ≤ h → raw.size = y * (rowBytes + 1) →
        (encodeIndexedRowsWithFilterLoop packedRows rowBytes h y prev raw strategy).size =
          h * (rowBytes + 1) := by
    intro k
    induction k with
    | zero =>
        intro y prev raw hk hy hraw
        have hge : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < h := not_lt_of_ge hge
        have hyEq : y = h := Nat.le_antisymm hy hge
        simp [encodeIndexedRowsWithFilterLoop, hraw, hyEq]
    | succ k ih =>
        intro y prev raw hk hy hraw
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy' : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        let row := packedRows.extract (y * rowBytes) (y * rowBytes + rowBytes)
        let filtered := filterRowForStrategy strategy row prev 1
        let raw' := raw.push filtered.1 ++ filtered.2
        have hrow : row.size = rowBytes := by
          simpa [row] using indexedPackedRow_extract_size packedRows rowBytes h y hpacked hlt
        have hfiltered : filtered.2.size = rowBytes := by
          have hsize := filterRowForStrategy_size strategy row prev 1
          simpa [filtered, hrow] using hsize
        have hraw' : raw'.size = (y + 1) * (rowBytes + 1) := by
          calc
            raw'.size = raw.size + 1 + filtered.2.size := by
              simp [raw', ByteArray.size_append, ByteArray.size_push, Nat.add_assoc]
            _ = y * (rowBytes + 1) + 1 + rowBytes := by
              rw [hraw, hfiltered]
            _ = y * (rowBytes + 1) + (rowBytes + 1) := by
              omega
            _ = (y + 1) * (rowBytes + 1) := by
              simp [Nat.add_mul, Nat.one_mul]
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have ih' := ih (y := y + 1) (prev := row) (raw := raw') hk' hy' hraw'
        have hdef :=
          congrArg ByteArray.size
            (encodeIndexedRowsWithFilterLoop.eq_1
              (packedRows := packedRows) (rowBytes := rowBytes) (h := h)
              (y := y) (prev := prev) (raw := raw) (strategy := strategy))
        calc
          (encodeIndexedRowsWithFilterLoop packedRows rowBytes h y prev raw strategy).size =
              (if y < h then
                encodeIndexedRowsWithFilterLoop packedRows rowBytes h (y + 1) row raw' strategy
               else raw).size := by
                simpa [row, filtered, raw'] using hdef
          _ = (encodeIndexedRowsWithFilterLoop packedRows rowBytes h (y + 1) row raw' strategy).size := by
                simp [hlt]
          _ = h * (rowBytes + 1) := ih'
  exact hk (h - y) y prev raw rfl hy hraw

/-- Indexed raw encoding emits one filter byte plus one packed row per image row.
This is the palette analogue of the existing raw encode size facts. -/
lemma encodeRawIndexedWithFilter_size (bmp : PngIndexedBitmap)
    (strategy : PngFilterStrategy) :
    (encodeRawIndexedWithFilter bmp strategy).size =
      bmp.size.height * (paletteRowBytes bmp.size.width bmp.bitDepth + 1) := by
  let rowBytes := paletteRowBytes bmp.size.width bmp.bitDepth
  have hraw : ByteArray.empty.size = 0 * (rowBytes + 1) := by simp
  have hpacked : (encodeIndexedPackedRows bmp).size = bmp.size.height * rowBytes := by
    simpa [rowBytes] using encodeIndexedPackedRows_size bmp
  unfold encodeRawIndexedWithFilter encodeIndexedRowsWithFilter
  by_cases hstrategy : strategy = PngFilterStrategy.none
  · let raw0 := ByteArray.mk <|
      Array.replicate (bmp.size.height * (rowBytes + 1)) (0 : UInt8)
    have hraw0 : raw0.size = bmp.size.height * (rowBytes + 1) := by
      simp [raw0, ByteArray.size, Array.size_replicate]
    have hloop :
        (encodeRawLoop (encodeIndexedPackedRows bmp) rowBytes bmp.size.height 0 raw0).size =
          raw0.size :=
      encodeRawLoop_size (data := encodeIndexedPackedRows bmp) (rowBytes := rowBytes)
        (h := bmp.size.height) (y := 0) (raw := raw0)
        (by simpa [rowBytes] using hpacked) hraw0
    have hcalc :
        (encodeRawLoop (encodeIndexedPackedRows bmp) rowBytes bmp.size.height 0 raw0).size =
          bmp.size.height * (rowBytes + 1) := by
      calc
        (encodeRawLoop (encodeIndexedPackedRows bmp) rowBytes bmp.size.height 0 raw0).size =
            raw0.size := hloop
        _ = bmp.size.height * (rowBytes + 1) := hraw0
    simpa [rowBytes, hstrategy, raw0] using hcalc
  · simpa [rowBytes, hstrategy] using
      encodeIndexedRowsWithFilterLoop_size
        (packedRows := encodeIndexedPackedRows bmp) (rowBytes := rowBytes)
        (h := bmp.size.height) (y := 0) (prev := ByteArray.empty)
        (raw := ByteArray.empty) (strategy := strategy) (by simpa [rowBytes] using hpacked)
        (Nat.zero_le _)
        hraw

/-- An empty indexed image emits no raw filtered rows.
This is the base case for palette raw-size reasoning. -/
lemma encodeRawIndexedWithFilter_empty_height (bmp : PngIndexedBitmap)
    (hheight : bmp.size.height = 0) :
    (encodeRawIndexedWithFilter bmp .none).size = 0 := by
  simpa [hheight] using encodeRawIndexedWithFilter_size bmp .none

/-- Filter-0 indexed row serialization is the existing byte-row raw encoder
when the packed index bytes are viewed as an 8-bit grayscale bitmap. -/
lemma encodeIndexedRowsWithFilter_none_eq_encodeRawGray8
    (packedRows : ByteArray) (w h : Nat) (hpacked : packedRows.size = h * w) :
    let rawBmp : BitmapGray8 :=
      { size := { width := w, height := h }
        data := packedRows
        valid := by
          calc
            packedRows.size = h * w := hpacked
            _ = w * h * Pixel.bytesPerPixel (α := PixelGray8) := by
                  simp [bytesPerPixel_gray, bytesPerPixelGray, Nat.mul_comm] }
    encodeIndexedRowsWithFilter packedRows w h .none = encodeRaw rawBmp := by
  intro rawBmp
  unfold encodeIndexedRowsWithFilter encodeRaw
  simp [rawBmp, bytesPerPixel_gray, bytesPerPixelGray]

/-- Decoding filter-0 8-bit indexed raw rows with a full palette reconstructs
the packed index byte stream. This is the raw-payload layer of palette round-trip
coverage, before proving the enclosing PNG chunk parser path. -/
lemma decodePaletteRowsLoop_encodeIndexedRowsWithFilter_none_8_256
    (packedRows : ByteArray) (w h : Nat) (hpacked : packedRows.size = h * w) :
    let raw := encodeIndexedRowsWithFilter packedRows w h .none
    let flat0 := ByteArray.mk <| Array.replicate (h * w) (0 : UInt8)
    decodePaletteRowsLoop raw w h 8 w 256 0 0 ByteArray.empty flat0 = some packedRows := by
  let rawBmp : BitmapGray8 :=
    { size := { width := w, height := h }
      data := packedRows
      valid := by
        calc
          packedRows.size = h * w := hpacked
          _ = w * h * Pixel.bytesPerPixel (α := PixelGray8) := by
                simp [bytesPerPixel_gray, bytesPerPixelGray, Nat.mul_comm] }
  let raw := encodeIndexedRowsWithFilter packedRows w h .none
  let flat0 := ByteArray.mk <| Array.replicate (h * w) (0 : UInt8)
  have hrawEq : raw = encodeRaw rawBmp := by
    simpa [raw, rawBmp] using
      encodeIndexedRowsWithFilter_none_eq_encodeRawGray8 packedRows w h hpacked
  have hdata : packedRows.size = h * w := hpacked
  have hraw : raw.size = h * (w + 1) := by
    calc
      raw.size = (encodeRaw rawBmp).size := by simp [hrawEq]
      _ = h * (w + 1) := by
            have hsize := encodeRaw_size (bmp := rawBmp)
            simpa [rawBmp, bytesPerPixel_gray, bytesPerPixelGray] using hsize
  have hflat0 : flat0.size = h * w := by
    simp [flat0, ByteArray.size, Array.size_replicate]
  let loop := decodePaletteRowsLoop raw w h 8 w 256
  have hk :
      ∀ k, ∀ y offset prevRow flat,
        h - y = k →
        y ≤ h →
        offset = y * (w + 1) →
        flat.size = h * w →
        flat.extract 0 (y * w) = packedRows.extract 0 (y * w) →
        loop y offset prevRow flat = some packedRows := by
    intro k
    induction k with
    | zero =>
        intro y offset prevRow flat hk hyLe hoff hflat hprefix
        have hyGe : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hyEq : y = h := Nat.le_antisymm hyLe hyGe
        have hlt : ¬ y < h := not_lt_of_ge hyGe
        have hoffsetRaw : offset = raw.size := by
          calc
            offset = y * (w + 1) := hoff
            _ = h * (w + 1) := by simp [hyEq]
            _ = raw.size := hraw.symm
        have hsize : flat.size = packedRows.size := by
          simpa [hdata] using hflat
        have hle : flat.size ≤ y * w := by
          have hmul : h * w ≤ y * w := Nat.mul_le_mul_right w hyGe
          simpa [hflat] using hmul
        have hprefix' :
            flat.extract 0 flat.size = packedRows.extract 0 flat.size := by
          exact
            byteArray_extract_eq_of_prefix_eq
              (a := flat) (b := packedRows) (n := y * w) (i := 0) (j := flat.size)
              hprefix hle
        have hflat_eq : flat = packedRows := by
          have hflat0' : flat.extract 0 flat.size = flat := by
            simp [ByteArray.extract_zero_size]
          have hdata0 : packedRows.extract 0 flat.size = packedRows := by
            have hdata0' : packedRows.extract 0 packedRows.size = packedRows := by
              simp [ByteArray.extract_zero_size]
            simp [hsize, hdata0']
          simpa [hflat0', hdata0] using hprefix'
        simp [loop, decodePaletteRowsLoop, hlt, hoffsetRaw, hflat_eq]
    | succ k ih =>
        intro y offset prevRow flat hk hyLe hoff hflat hprefix
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy' : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        have hofflt : offset < raw.size := by
          have hmul : y * (w + 1) < h * (w + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (by omega)
          simpa [hoff, hraw] using hmul
        have hrowBound : offset + 1 + w ≤ raw.size := by
          have hmul : (y + 1) * (w + 1) ≤ h * (w + 1) :=
            Nat.mul_le_mul_right (w + 1) hy'
          have hmul' : (y + 1) * (w + 1) ≤ raw.size := by
            simpa [hraw] using hmul
          have hcalc : offset + 1 + w = (y + 1) * (w + 1) := by
            calc
              offset + 1 + w = y * (w + 1) + (w + 1) := by
                simp [hoff, Nat.add_assoc, Nat.add_comm]
              _ = (y + 1) * (w + 1) := by
                simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
          simpa [hcalc] using hmul'
        have hfilter0 : raw.get! offset = 0 := by
          have hzero := encodeRaw_filter_zero (bmp := rawBmp) (y := y) hlt
          simpa [raw, hrawEq, rawBmp, bytesPerPixel_gray, bytesPerPixelGray, hoff] using hzero
        have hrowData :
            raw.extract (offset + 1) (offset + 1 + w) =
              packedRows.extract (y * w) (y * w + w) := by
          have hrow := encodeRaw_row_extract (bmp := rawBmp) (y := y) hlt
          simpa [raw, hrawEq, rawBmp, bytesPerPixel_gray, bytesPerPixelGray, hoff] using hrow
        let rowData := raw.extract (offset + 1) (offset + 1 + w)
        have hrowData' :
            rowData = packedRows.extract (y * w) (y * w + w) := by
          simpa [rowData] using hrowData
        have hrowDataSize : rowData.size = w := by
          simp [rowData, ByteArray.size_extract, Nat.min_eq_left hrowBound]
        have hdestFlat : y * w + w ≤ flat.size := by
          have hmul : (y + 1) * w ≤ h * w :=
            Nat.mul_le_mul_right w hy'
          have hmul' : (y + 1) * w ≤ flat.size := by
            simpa [hflat] using hmul
          simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
        let rowOffset := y * w
        let flat' := rowData.copySlice 0 flat rowOffset w
        have hmid :
            flat'.extract rowOffset (rowOffset + w) =
              packedRows.extract (y * w) (y * w + w) := by
          have hsrc : 0 + w ≤ rowData.size := by
            simp [hrowDataSize]
          have hdest : rowOffset + w ≤ flat.size := hdestFlat
          have hrowData0 : rowData.extract 0 w = rowData := by
            have hzero : rowData.extract 0 rowData.size = rowData := by
              simp [ByteArray.extract_zero_size]
            simpa [hrowDataSize] using hzero
          calc
            flat'.extract rowOffset (rowOffset + w) =
                rowData.extract 0 w := by
                  simpa [flat', rowOffset] using
                    byteArray_copySlice_extract_mid (src := rowData) (dest := flat)
                      (srcOff := 0) (destOff := rowOffset) (len := w) hsrc hdest
            _ = rowData := hrowData0
            _ = packedRows.extract (y * w) (y * w + w) := hrowData'
        have hpre' :
            flat'.extract 0 rowOffset = flat.extract 0 rowOffset := by
          have hdest : rowOffset + w ≤ flat.size := hdestFlat
          simpa [flat', rowOffset] using
            byteArray_copySlice_extract_prefix (src := rowData) (dest := flat)
              (srcOff := 0) (destOff := rowOffset) (len := w) hdest
        have hprefix' :
            flat'.extract 0 ((y + 1) * w) =
              packedRows.extract 0 ((y + 1) * w) := by
          have hnm : rowOffset ≤ rowOffset + w := by omega
          have hsrc : 0 + w ≤ rowData.size := by
            simp [hrowDataSize]
          have hdest : rowOffset + w ≤ flat.size := hdestFlat
          have hsizeFlat' : flat'.size = flat.size := by
            simpa [flat'] using
              byteArray_copySlice_size (src := rowData) (dest := flat)
                (srcOff := 0) (destOff := rowOffset) (len := w) hsrc hdest
          have ha : rowOffset + w ≤ flat'.size := by
            simpa [hsizeFlat'] using hdestFlat
          have hb : rowOffset + w ≤ packedRows.size := by
            have hmul : (y + 1) * w ≤ h * w :=
              Nat.mul_le_mul_right w hy'
            simpa [hdata, rowOffset, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
              using hmul
          have hpref :
              flat'.extract 0 rowOffset = packedRows.extract 0 rowOffset := by
            simpa [rowOffset] using hpre'.trans hprefix
          have hprefix'' :
              flat'.extract 0 (rowOffset + w) =
                packedRows.extract 0 (rowOffset + w) := by
            exact
              byteArray_extract_prefix_extend (a := flat') (b := packedRows) (n := rowOffset)
                (m := rowOffset + w) hnm ha hb hpref hmid
          simpa [rowOffset, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
            using hprefix''
        have hflat' : flat'.size = h * w := by
          have hsrc : 0 + w ≤ rowData.size := by
            simp [hrowDataSize]
          have hdest : rowOffset + w ≤ flat.size := hdestFlat
          have hsizeFlat' : flat'.size = flat.size := by
            simpa [flat'] using
              byteArray_copySlice_size (src := rowData) (dest := flat)
                (srcOff := 0) (destOff := rowOffset) (len := w) hsrc hdest
          simpa [hflat] using hsizeFlat'
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have hoff' : offset + 1 + w = (y + 1) * (w + 1) := by
          calc
            offset + 1 + w = y * (w + 1) + (w + 1) := by
              simp [hoff, Nat.add_assoc, Nat.add_comm]
            _ = (y + 1) * (w + 1) := by
              simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
        have hnext :
            loop (y + 1) (offset + 1 + w) rowData flat' = some packedRows := by
          exact ih (y := y + 1) (offset := offset + 1 + w) (prevRow := rowData)
            (flat := flat') hk' hy' hoff' hflat' hprefix'
        have hgoal :
            loop y offset prevRow flat =
              loop (y + 1) (offset + 1 + w) rowData flat' := by
          dsimp [loop]
          rw [decodePaletteRowsLoop.eq_1]
          simp [hlt, hrowBound, hfilter0, rowData, rowOffset, flat',
            paletteScatterFullRow_8_256]
        exact hgoal.trans hnext
  have hstart :=
    hk (h - 0) (y := 0) (offset := 0) (prevRow := ByteArray.empty)
      (flat := flat0) rfl (Nat.zero_le _) (by simp) hflat0 (by simp)
  simpa [raw, flat0] using hstart

/-- The non-interlaced indexed raw decoder accepts filter-0 8-bit rows with a
full palette and returns the packed index bytes unchanged. This is the public
raw decoder wrapper around `decodePaletteRowsLoop_encode...`. -/
lemma decodePaletteIndicesByInterlace_encodeIndexedRowsWithFilter_none_8_256
    (packedRows : ByteArray) (w h : Nat) (hpacked : packedRows.size = h * w) :
    let hdr : PngHeader :=
      { width := w, height := h, colorType := 3, bitDepth := 8, interlace := 0 }
    decodePaletteIndicesByInterlace?
      (encodeIndexedRowsWithFilter packedRows w h .none) hdr 256 = some packedRows := by
  intro hdr
  have hloop :=
    decodePaletteRowsLoop_encodeIndexedRowsWithFilter_none_8_256 packedRows w h hpacked
  have hrowBytes : (w * 8 + 7) / 8 = w := by
    simpa [paletteRowBytes] using paletteRowBytes_8 w
  unfold decodePaletteIndicesByInterlace?
  simpa [hdr, hrowBytes, Nat.mul_comm] using hloop

/-- An 8-bit indexed bitmap encoded as filter-0 raw rows decodes back to its
index bytes when decoded as a non-interlaced full-palette image. This is the
bitmap-shaped raw round-trip layer below the full PNG container theorem. -/
lemma decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_256
    (bmp : PngIndexedBitmap) (hbd : bmp.bitDepth = 8) :
    let hdr : PngHeader :=
      { width := bmp.size.width, height := bmp.size.height, colorType := 3,
        bitDepth := 8, interlace := 0 }
    decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none) hdr 256 =
      some bmp.data := by
  intro hdr
  have hpacked : bmp.data.size = bmp.size.height * bmp.size.width := by
    calc
      bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
      _ = bmp.size.height * bmp.size.width := by rw [Nat.mul_comm]
  have hpack := encodeIndexedPackedRows_8_eq_data bmp hbd
  have hrowBytes : paletteRowBytes bmp.size.width bmp.bitDepth = bmp.size.width := by
    simpa [hbd] using paletteRowBytes_8 bmp.size.width
  have hrowBytesExpr : (bmp.size.width * bmp.bitDepth + 7) / 8 = bmp.size.width := by
    simpa [paletteRowBytes] using hrowBytes
  have hraw :
      encodeRawIndexedWithFilter bmp .none =
        encodeIndexedRowsWithFilter bmp.data bmp.size.width bmp.size.height .none := by
    unfold encodeRawIndexedWithFilter
    simp [hpack, hrowBytesExpr]
  have hdecode :=
    decodePaletteIndicesByInterlace_encodeIndexedRowsWithFilter_none_8_256
      bmp.data bmp.size.width bmp.size.height hpacked
  simpa [hdr, hraw] using hdecode

/-- A parsed non-interlaced 8-bit indexed PNG with stored zlib IDAT and a full
palette decodes back to the bitmap's index bytes. This composes the raw
palette theorem with the stored zlib envelope, still below chunk parsing. -/
lemma decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_256_data
    (bmp : PngIndexedBitmap) (hbd : bmp.bitDepth = 8)
    (hpal : bmp.palette.entryCount = 256) :
    let metadata : PngMetadata := { PngMetadata.empty with palette := some bmp.palette }
    let parsed : PngParsed :=
      { header :=
          { width := bmp.size.width, height := bmp.size.height, colorType := 3,
            bitDepth := 8, interlace := 0 }
        idat := zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
        metadata := metadata }
    (decodeParsedIndexedBitmapWithMetadata parsed).map (fun result => result.bitmap.data) =
      some bmp.data := by
  intro metadata parsed
  have hraw :=
    decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_256 bmp hbd
  have hrawPal :
      decodePaletteIndicesByInterlace? (encodeRawIndexedWithFilter bmp .none)
        { width := bmp.size.width, height := bmp.size.height, colorType := 3,
          bitDepth := 8, interlace := 0 }
        bmp.palette.entryCount = some bmp.data := by
    simpa [hpal] using hraw
  have hsize6 := zlibCompressStored_size_ge (encodeRawIndexedWithFilter bmp .none)
  have hsize2 : 2 ≤ (zlibCompressStored (encodeRawIndexedWithFilter bmp .none)).size := by
    omega
  have hvalid : bmp.data.size = bmp.size.width * bmp.size.height := bmp.valid
  unfold decodeParsedIndexedBitmapWithMetadata
  simp [parsed, metadata, PngMetadata.empty, hsize2, hvalid, hrawPal,
    zlibDecompressStored_zlibCompressStored, pngColorTypeBitDepthSupported]

end Lemmas

end Bitmaps
