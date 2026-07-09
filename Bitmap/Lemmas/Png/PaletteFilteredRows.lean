import Bitmap.Lemmas.Png.Palette
import Bitmap.Lemmas.Png.CoreByteArray

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Symbolic filtered-row bridge for indexed palette decoding

This module abstracts the row-filter part of palette decoding away from the
concrete fixture PNGs.  A caller supplies the same per-row reconstruction
contract used by the decoder; the theorem then proves that the palette row loop
reconstructs the indexed data for arbitrary valid filtered row streams. -/

/-- Per-row contract for palette row decoding. For each serialized PNG row,
the filter byte is valid and reconstructing the row payload against the previous
decoded row yields the matching packed palette row slice. -/
def paletteRowDecoderContract (raw packedRows : ByteArray) (h rowBytes : Nat) : Prop :=
  ∀ y, y < h →
    let offset := y * (rowBytes + 1)
    let filter := raw.get! offset
    let rowData := raw.extract (offset + 1) (offset + 1 + rowBytes)
    let prev :=
      if y = 0 then ByteArray.empty
      else packedRows.extract ((y - 1) * rowBytes) (y * rowBytes)
    let slice := packedRows.extract (y * rowBytes) ((y + 1) * rowBytes)
    ∃ (hfilter : filter.toNat ≤ 4),
      (if filter.toNat = 0 then rowData
       else unfilterRow filter rowData prev 1 hfilter) = slice

set_option maxHeartbeats 16000000 in
/-- Palette row decoding succeeds for any non-fast-path filtered row stream
whose reconstructed rows match a packed indexed-row buffer. This replaces
fixture-level fixed/adaptive filter coverage with a symbolic row contract. -/
theorem decodePaletteRowsLoop_eq_of_paletteRowDecoderContract_nonfast
    (raw data packedRows : ByteArray)
    (w h bitDepth rowBytes paletteEntries : Nat)
    (hLayout : raw.size = h * (rowBytes + 1))
    (hdata : data.size = w * h)
    (hnotFast : ¬ (bitDepth = 8 ∧ 256 ≤ paletteEntries))
    (hpackedIndex :
      ∀ y, y < h → ∀ x, x < w →
        palettePackedIndexAt
          (packedRows.extract (y * rowBytes) (y * rowBytes + rowBytes))
          bitDepth x = data.get! (y * w + x))
    (hrange :
      ∀ y, y < h → ∀ x, x < w →
        (data.get! (y * w + x)).toNat < paletteEntries)
    (hContract : paletteRowDecoderContract raw packedRows h rowBytes) :
    let flat0 := ByteArray.mk <| Array.replicate (w * h) 0
    decodePaletteRowsLoop raw w h bitDepth rowBytes paletteEntries 0 0
      ByteArray.empty flat0 = some data := by
  intro flat0
  have hflat0 : flat0.size = w * h := by
    simp [flat0, ByteArray.size, Array.size_replicate]
  let prevAt : Nat → ByteArray := fun y =>
    if y = 0 then ByteArray.empty
    else packedRows.extract ((y - 1) * rowBytes) (y * rowBytes)
  have hk :
      ∀ k, ∀ y offset flat,
        h - y = k →
        y ≤ h →
        offset = y * (rowBytes + 1) →
        flat.size = w * h →
        (∀ yy, yy < y → ∀ x, x < w →
          flat.get! (yy * w + x) = data.get! (yy * w + x)) →
        decodePaletteRowsLoop raw w h bitDepth rowBytes paletteEntries y offset
          (prevAt y) flat = some data := by
    intro k
    induction k with
    | zero =>
        intro y offset flat hk hy hoff hflat hprefix
        have hyGe : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hyEq : y = h := Nat.le_antisymm hy hyGe
        have hlt : ¬ y < h := not_lt_of_ge hyGe
        have hoffsetRaw : offset = raw.size := by
          calc
            offset = y * (rowBytes + 1) := hoff
            _ = h * (rowBytes + 1) := by simp [hyEq]
            _ = raw.size := hLayout.symm
        have hflatEq : flat = data := by
          have hsize : flat.size = data.size := by
            calc
              flat.size = w * h := hflat
              _ = data.size := hdata.symm
          refine Png.byteArray_eq_of_size_get! flat data hsize ?_
          intro i hi
          by_cases hw : w = 0
          · have hflatZero : flat.size = 0 := by
              simpa [hw] using hflat
            omega
          · have hwpos : 0 < w := Nat.pos_of_ne_zero hw
            have hiData : i < w * h := by
              simpa [hflat] using hi
            have hyi : i / w < h := by
              apply Nat.div_lt_of_lt_mul
              simpa [Nat.mul_comm] using hiData
            have hxi : i % w < w := Nat.mod_lt i hwpos
            have hidx : i / w * w + i % w = i := by
              have h := Nat.mod_add_div i w
              simpa [Nat.add_comm, Nat.mul_comm] using h
            have hget :=
              hprefix (i / w) (by simpa [hyEq] using hyi) (i % w) hxi
            simpa [hidx] using hget
        simp [decodePaletteRowsLoop, hlt, hoffsetRaw, hflatEq]
    | succ k ih =>
        intro y offset flat hk hy hoff hflat hprefix
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy' : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        have hrowBound : offset + 1 + rowBytes ≤ raw.size := by
          have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
            Nat.mul_le_mul_right (rowBytes + 1) hy'
          have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
            simpa [hLayout] using hmul
          have hcalc : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
            calc
              offset + 1 + rowBytes = y * (rowBytes + 1) + (rowBytes + 1) := by
                simp [hoff, Nat.add_assoc, Nat.add_comm]
              _ = (y + 1) * (rowBytes + 1) := by
                simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
          simpa [hcalc] using hmul'
        let rowData := raw.extract (offset + 1) (offset + 1 + rowBytes)
        have hContractY := hContract y hlt
        rcases hContractY with ⟨hfilter, hRow⟩
        have hfilterRaw : (raw.get! offset).toNat ≤ 4 := by
          simpa [hoff] using hfilter
        let row :=
          if (raw.get! offset).toNat = 0 then rowData
          else unfilterRow (raw.get! offset) rowData (prevAt y) 1 hfilterRaw
        have hrowPacked :
            row = packedRows.extract (y * rowBytes) ((y + 1) * rowBytes) := by
          have hPrev : (prevAt y : ByteArray) =
              if y = 0 then ByteArray.empty
              else packedRows.extract ((y - 1) * rowBytes) (y * rowBytes) := rfl
          simpa [row, rowData, hoff, hPrev] using hRow
        have hrowRange :
            ∀ z, z < w → (palettePackedIndexAt row bitDepth z).toNat < paletteEntries := by
          intro z hz
          have hpackedAt :
              palettePackedIndexAt row bitDepth z = data.get! (y * w + z) := by
            simpa [hrowPacked, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
              using hpackedIndex y hlt z hz
          simpa [hpackedAt] using hrange y hlt z hz
        have hscatterSuccess :
            ∃ flatNext,
              paletteScatterFullRow row flat w bitDepth y paletteEntries =
                some flatNext :=
          paletteScatterFullRow_succeeds_of_rowRange_nonfast row flat w bitDepth
            y paletteEntries hnotFast hrowRange
        rcases hscatterSuccess with ⟨flatNext, hscatter⟩
        have hflatNext : flatNext.size = w * h := by
          calc
            flatNext.size = flat.size :=
              paletteScatterFullRow_size_of_some_nonfast row flat flatNext w
                bitDepth y paletteEntries hnotFast hscatter
            _ = w * h := hflat
        have hprefix' :
            ∀ yy, yy < y + 1 → ∀ x, x < w →
              flatNext.get! (yy * w + x) = data.get! (yy * w + x) := by
          intro yy hyy x hx
          by_cases hprev : yy < y
          · have hi : yy * w + x < y * w := by
              have hsucc : yy + 1 ≤ y := Nat.succ_le_of_lt hprev
              have hmul : (yy + 1) * w ≤ y * w :=
                Nat.mul_le_mul_right w hsucc
              have hltx : yy * w + x < (yy + 1) * w := by
                have hx' : yy * w + x < yy * w + w :=
                  Nat.add_lt_add_left hx (yy * w)
                simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hx'
              exact Nat.lt_of_lt_of_le hltx hmul
            rcases
              paletteScatterFullRow_preserves_lt_rowStart_of_rowRange_nonfast
                row flat w bitDepth y paletteEntries (yy * w + x) hnotFast
                hrowRange hi with
              ⟨out, hout, hget⟩
            rw [hscatter] at hout
            cases hout
            exact hget.trans (hprefix yy hprev x hx)
          · have hyyEq : yy = y := by omega
            rcases
              paletteScatterFullRow_get!_of_rowRange_nonfast row flat w bitDepth
                y paletteEntries x hx hnotFast hrowRange
                (by
                  intro z hz
                  change y * w + z < flat.size
                  have hltRow : y * w + z < (y + 1) * w := by
                    have hz' : y * w + z < y * w + w :=
                      Nat.add_lt_add_left hz (y * w)
                    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hz'
                  have hrowLe : (y + 1) * w ≤ h * w :=
                    Nat.mul_le_mul_right w hy'
                  have hflatBound : y * w + z < w * h := by
                    have h := Nat.lt_of_lt_of_le hltRow hrowLe
                    simpa [Nat.mul_comm] using h
                  simpa [hflat] using hflatBound) with
              ⟨out, hout, hget⟩
            rw [hscatter] at hout
            cases hout
            have hpackedAt :
                palettePackedIndexAt row bitDepth x = data.get! (y * w + x) := by
              simpa [hrowPacked, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
                using hpackedIndex y hlt x hx
            have hget' :
                flatNext.get! (y * w + x) = palettePackedIndexAt row bitDepth x := by
              change flatNext.get! (y * w + x) = palettePackedIndexAt row bitDepth x at hget
              exact hget
            simpa [hyyEq] using hget'.trans hpackedAt
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have hoff' : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
          calc
            offset + 1 + rowBytes = y * (rowBytes + 1) + (rowBytes + 1) := by
              simp [hoff, Nat.add_assoc, Nat.add_comm]
            _ = (y + 1) * (rowBytes + 1) := by
              simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
        have hPrevNext : prevAt (y + 1) = row := by
          show (if y + 1 = 0 then ByteArray.empty
            else packedRows.extract ((y + 1 - 1) * rowBytes) ((y + 1) * rowBytes)) = row
          have hne : y + 1 ≠ 0 := by omega
          simp [hrowPacked]
        have hnext :
            decodePaletteRowsLoop raw w h bitDepth rowBytes paletteEntries
              (y + 1) (offset + 1 + rowBytes) (prevAt (y + 1)) flatNext =
                some data :=
          ih (y := y + 1) (offset := offset + 1 + rowBytes) (flat := flatNext)
            hk' hy' hoff' hflatNext hprefix'
        rw [decodePaletteRowsLoop.eq_1]
        simp [hlt, hrowBound, hfilterRaw, rowData, row, hscatter]
        change decodePaletteRowsLoop raw w h bitDepth rowBytes paletteEntries
          (y + 1) (offset + 1 + rowBytes) row flatNext = some data
        rw [← hPrevNext]
        exact hnext
  have hstart :=
    hk (h - 0) (y := 0) (offset := 0) (flat := flat0)
      rfl (Nat.zero_le _) (by simp) hflat0 (by intro yy hyy; omega)
  have hPrev0 : prevAt 0 = ByteArray.empty := by simp [prevAt]
  simpa [hPrev0] using hstart

end Lemmas

end Bitmaps
