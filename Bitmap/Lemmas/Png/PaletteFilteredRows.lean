import Bitmap.Lemmas.Png.Palette
import Bitmap.Lemmas.Png.CoreByteArray
import Bitmap.Lemmas.Png.RowFilterInverse

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

private def paletteRowContractAt (raw packedRows : ByteArray)
    (rowBytes y : Nat) : Prop :=
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

/-- The tail-recursive indexed row encoder preserves its accumulated raw prefix.
This lets later row appends be ignored when proving a previous row block. -/
private lemma encodeIndexedRowsWithFilterLoop_extract_prefix
    (packedRows : ByteArray) (rowBytes h y : Nat) (prev raw : ByteArray)
    (strategy : PngFilterStrategy) :
    (encodeIndexedRowsWithFilterLoop packedRows rowBytes h y prev raw strategy).extract
        0 raw.size = raw := by
  have hk :
      ∀ k, ∀ y prev raw,
        h - y = k →
        (encodeIndexedRowsWithFilterLoop packedRows rowBytes h y prev raw strategy).extract
            0 raw.size = raw := by
    intro k
    induction k with
    | zero =>
        intro y prev raw hk
        have hge : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < h := not_lt_of_ge hge
        simp [encodeIndexedRowsWithFilterLoop, hlt, ByteArray.extract_zero_size]
    | succ k ih =>
        intro y prev raw hk
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        let row := packedRows.extract (y * rowBytes) (y * rowBytes + rowBytes)
        let filtered := filterRowForStrategy strategy row prev 1
        let raw' := raw.push filtered.1 ++ filtered.2
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have hprefix' :
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h (y + 1) row raw' strategy).extract
                0 raw'.size = raw' :=
          ih (y := y + 1) (prev := row) (raw := raw') hk'
        have hrawLe : raw.size ≤ raw'.size := by
          simp [raw', ByteArray.size_append, ByteArray.size_push]
          omega
        have hslice :
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h (y + 1) row raw' strategy).extract
                0 raw.size = raw'.extract 0 raw.size :=
          Png.byteArray_extract_slice_of_prefix
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h (y + 1) row raw' strategy)
            raw' raw'.size 0 raw.size hprefix' hrawLe
        have hraw'Prefix : raw'.extract 0 raw.size = raw := by
          calc
            raw'.extract 0 raw.size =
                ((raw.push filtered.1) ++ filtered.2).extract 0 raw.size := by rfl
            _ = (raw.push filtered.1).extract 0 raw.size := by
                exact
                  Png.byteArray_extract_append_prefix (raw.push filtered.1) filtered.2
                    raw.size (by simp [ByteArray.size_push])
            _ = raw := Png.byteArray_extract_push_prefix raw filtered.1
        have hdef :=
          congrArg (fun b => b.extract 0 raw.size)
            (encodeIndexedRowsWithFilterLoop.eq_1
              (packedRows := packedRows) (rowBytes := rowBytes) (h := h)
              (y := y) (prev := prev) (raw := raw) (strategy := strategy))
        calc
          (encodeIndexedRowsWithFilterLoop packedRows rowBytes h y prev raw strategy).extract
              0 raw.size =
              (if y < h then
                encodeIndexedRowsWithFilterLoop packedRows rowBytes h (y + 1) row raw' strategy
               else raw).extract 0 raw.size := by
                simpa [row, filtered, raw'] using hdef
          _ = (encodeIndexedRowsWithFilterLoop packedRows rowBytes h (y + 1) row raw' strategy).extract
                0 raw.size := by simp [hlt]
          _ = raw := by rw [hslice, hraw'Prefix]
  exact hk (h - y) y prev raw rfl

set_option maxHeartbeats 12000000 in
/-- Starting from any row in the indexed filtered encoder, the final serialized
stream satisfies the decoder row contract at every later target row. This is
the induction bridge from encoder layout to the palette decoder contract. -/
private lemma encodeIndexedRowsWithFilterLoop_row_contract_from
    (packedRows : ByteArray) (rowBytes h target start : Nat)
    (prev raw : ByteArray) (strategy : PngFilterStrategy)
    (hpacked : packedRows.size = h * rowBytes)
    (hstart : start ≤ target) (htarget : target < h)
    (hraw : raw.size = start * (rowBytes + 1))
    (hprev :
      prev =
        if start = 0 then ByteArray.empty
        else packedRows.extract ((start - 1) * rowBytes) (start * rowBytes)) :
    paletteRowContractAt
      (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy)
      packedRows rowBytes target := by
  have hk :
      ∀ k, ∀ (start : Nat) (prev raw : ByteArray),
        target - start = k →
        start ≤ target →
        raw.size = start * (rowBytes + 1) →
        (prev =
          (if start = 0 then ByteArray.empty
          else packedRows.extract ((start - 1) * rowBytes) (start * rowBytes))) →
        paletteRowContractAt
          (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy)
          packedRows rowBytes target := by
    intro k
    induction k with
    | zero =>
        intro start prev raw hk hstart hraw hprev
        have hge : target ≤ start := Nat.le_of_sub_eq_zero hk
        have hEq : target = start := Nat.le_antisymm hge hstart
        subst target
        let row := packedRows.extract (start * rowBytes) (start * rowBytes + rowBytes)
        let filtered := filterRowForStrategy strategy row prev 1
        let raw' := raw.push filtered.1 ++ filtered.2
        have hrowSize : row.size = rowBytes := by
          simpa [row] using indexedPackedRow_extract_size packedRows rowBytes h start hpacked htarget
        have hfilteredSize : filtered.2.size = rowBytes := by
          have hsize := filterRowForStrategy_size strategy row prev 1
          simpa [filtered, hrowSize] using hsize
        have hraw'SizeAdd : raw'.size = raw.size + 1 + filtered.2.size := by
          simp [raw', ByteArray.size_append, ByteArray.size_push, Nat.add_assoc]
        have hraw'Size : raw'.size = (start + 1) * (rowBytes + 1) := by
          calc
            raw'.size = raw.size + 1 + filtered.2.size := hraw'SizeAdd
            _ = start * (rowBytes + 1) + 1 + rowBytes := by rw [hraw, hfilteredSize]
            _ = start * (rowBytes + 1) + (rowBytes + 1) := by omega
            _ = (start + 1) * (rowBytes + 1) := by
                simp [Nat.add_mul, Nat.one_mul]
        have hoffsetEq : start * (rowBytes + 1) = raw.size := hraw.symm
        have hfilterInPrefix : raw.size < raw'.size := by
          rw [hraw'SizeAdd]
          omega
        have hrowDataInPrefix : raw.size + 1 + rowBytes ≤ raw'.size := by
          rw [hraw'SizeAdd, hfilteredSize]
        have hfinalEq :
            encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy =
              encodeIndexedRowsWithFilterLoop packedRows rowBytes h (start + 1) row raw' strategy := by
          rw [encodeIndexedRowsWithFilterLoop.eq_1]
          simp [htarget, row, filtered, raw']
        have hprefixRec :
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h (start + 1) row raw' strategy).extract
                0 raw'.size = raw' :=
          encodeIndexedRowsWithFilterLoop_extract_prefix packedRows rowBytes h
            (start + 1) row raw' strategy
        have hprefixFinal :
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).extract
                0 raw'.size = raw' := by
          rw [hfinalEq]
          exact hprefixRec
        have hfilterEq :
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).get!
                (start * (rowBytes + 1)) = filtered.1 := by
          calc
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).get!
                (start * (rowBytes + 1)) =
                (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).get!
                  raw.size := by rw [hoffsetEq]
            _ = raw'.get! raw.size :=
                Png.byteArray_get!_of_prefix
                  (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy)
                  raw' raw'.size raw.size hprefixFinal hfilterInPrefix
            _ = ((raw.push filtered.1) ++ filtered.2).get! raw.size := by rfl
            _ = (raw.push filtered.1).get! raw.size :=
                Png.byteArray_get!_append_left (raw.push filtered.1) filtered.2
                  raw.size (by simp [ByteArray.size_push])
            _ = filtered.1 := Png.byteArray_get!_push_eq raw filtered.1
        have hrowDataEq :
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).extract
                (start * (rowBytes + 1) + 1)
                (start * (rowBytes + 1) + 1 + rowBytes) = filtered.2 := by
          have hslicePrefix :
              (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).extract
                  (raw.size + 1) (raw.size + 1 + rowBytes) =
                raw'.extract (raw.size + 1) (raw.size + 1 + rowBytes) :=
            Png.byteArray_extract_slice_of_prefix
              (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy)
              raw' raw'.size (raw.size + 1) (raw.size + 1 + rowBytes)
              hprefixFinal hrowDataInPrefix
          have hmiddle : raw'.extract (raw.size + 1) (raw.size + 1 + rowBytes) = filtered.2 := by
            have hpushSize : (raw.push filtered.1).size = raw.size + 1 := by
              simp [ByteArray.size_push]
            have hmid :=
              Png.byteArray_extract_append_middle_full
                (raw.push filtered.1) filtered.2 ByteArray.empty
            simpa [raw', hpushSize, hfilteredSize] using hmid
          calc
            (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).extract
                (start * (rowBytes + 1) + 1)
                (start * (rowBytes + 1) + 1 + rowBytes) =
                (encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy).extract
                  (raw.size + 1) (raw.size + 1 + rowBytes) := by rw [hoffsetEq]
            _ = raw'.extract (raw.size + 1) (raw.size + 1 + rowBytes) := hslicePrefix
            _ = filtered.2 := hmiddle
        have hsliceEq :
            packedRows.extract (start * rowBytes) ((start + 1) * rowBytes) = row := by
          simp [row, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rcases filterRowForStrategy_decodes_one_byte_distance strategy row prev with
          ⟨hfilter, hdecode⟩
        refine ⟨by simpa [paletteRowContractAt, hfilterEq] using hfilter, ?_⟩
        simpa [paletteRowContractAt, hfilterEq, hrowDataEq, hprev.symm, hsliceEq] using hdecode
    | succ k ih =>
        intro start prev raw hk hstart hraw hprev
        have hltTarget : start < target := Nat.lt_of_sub_eq_succ hk
        have hltHeight : start < h := Nat.lt_trans hltTarget htarget
        let row := packedRows.extract (start * rowBytes) (start * rowBytes + rowBytes)
        let filtered := filterRowForStrategy strategy row prev 1
        let raw' := raw.push filtered.1 ++ filtered.2
        have hrowSize : row.size = rowBytes := by
          simpa [row] using indexedPackedRow_extract_size packedRows rowBytes h start hpacked hltHeight
        have hfilteredSize : filtered.2.size = rowBytes := by
          have hsize := filterRowForStrategy_size strategy row prev 1
          simpa [filtered, hrowSize] using hsize
        have hraw' : raw'.size = (start + 1) * (rowBytes + 1) := by
          calc
            raw'.size = raw.size + 1 + filtered.2.size := by
              simp [raw', ByteArray.size_append, ByteArray.size_push, Nat.add_assoc]
            _ = start * (rowBytes + 1) + 1 + rowBytes := by rw [hraw, hfilteredSize]
            _ = start * (rowBytes + 1) + (rowBytes + 1) := by omega
            _ = (start + 1) * (rowBytes + 1) := by
                simp [Nat.add_mul, Nat.one_mul]
        have hk' : target - (start + 1) = k := by
          have hsum : target = Nat.succ k + start := Nat.eq_add_of_sub_eq hstart hk
          calc
            target - (start + 1) = (Nat.succ k + start) - (start + 1) := by simp [hsum]
            _ = k := by omega
        have hstart' : start + 1 ≤ target := Nat.succ_le_of_lt hltTarget
        have hprevNext :
            row =
              if start + 1 = 0 then ByteArray.empty
              else packedRows.extract ((start + 1 - 1) * rowBytes) ((start + 1) * rowBytes) := by
          simp [row, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        have hnext :
            paletteRowContractAt
              (encodeIndexedRowsWithFilterLoop packedRows rowBytes h (start + 1) row raw' strategy)
              packedRows rowBytes target :=
          ih (start := start + 1) (prev := row) (raw := raw')
            hk' hstart' hraw' hprevNext
        have hdef :
            encodeIndexedRowsWithFilterLoop packedRows rowBytes h start prev raw strategy =
              encodeIndexedRowsWithFilterLoop packedRows rowBytes h (start + 1) row raw' strategy := by
          rw [encodeIndexedRowsWithFilterLoop.eq_1]
          simp [hltHeight, row, filtered, raw']
        simpa [hdef] using hnext
  exact hk (target - start) start prev raw rfl hstart hraw hprev

/-- The fixed/adaptive indexed row encoder emits a raw stream satisfying the
palette decoder's row contract. Each packed row is reconstructed exactly by
the decoder's byte-distance-one PNG filters. -/
theorem paletteRowDecoderContract_encodeIndexedRowsWithFilterLoop
    (packedRows : ByteArray) (rowBytes h : Nat) (strategy : PngFilterStrategy)
    (hpacked : packedRows.size = h * rowBytes) :
    paletteRowDecoderContract
      (encodeIndexedRowsWithFilterLoop packedRows rowBytes h 0 ByteArray.empty
        ByteArray.empty strategy)
      packedRows h rowBytes := by
  intro y hy
  simpa [paletteRowDecoderContract, paletteRowContractAt] using
    encodeIndexedRowsWithFilterLoop_row_contract_from
      (packedRows := packedRows) (rowBytes := rowBytes) (h := h)
      (target := y) (start := 0) (prev := ByteArray.empty)
      (raw := ByteArray.empty) (strategy := strategy) hpacked (Nat.zero_le y) hy
      (by simp) (by simp)

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
