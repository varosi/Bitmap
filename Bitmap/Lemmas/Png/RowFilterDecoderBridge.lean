import Bitmap.Lemmas.Png.RowFilterSpec
import Bitmap.Lemmas.Png.CoreByteArray
import Bitmap.Lemmas.Png.EncodeDecodeBase

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Phase 5.5 — Row-filter spec ↔ `decodeRowsLoopCore` bridge

`reconstructRowsAccSpec` (Phase 4) gives the pure pixel-buffer
reconstruction from a filtered row stream; `decodeRowsLoopCore`
(runtime) implements the same loop via `copySlice` into a
pre-allocated buffer. This file bridges them for the same-`bpp`
branch: under valid filter bytes and a layout-matching raw stream,
the runtime decoder returns the spec's accumulated pixel buffer.

The bridge lets Phase 5 (and future Phase 8–11) clients build
`hPixels`-style witnesses mechanically from row-filter facts rather
than supplying the runtime equation by hand. -/

/-! ### Per-row decoder contract

A unified statement matching what `decodeRowsLoopCore`'s same-`bpp`
branch computes for one row. For filter byte 0 the runtime
short-circuits to `rowData`; for filter bytes 1–4 it calls
`unfilterRow`. The contract below packages both into the same
"per-row reconstruction matches the target slice" form.

Downstream clients can discharge each disjunct via the existing
`unfilterRow_eq_spec` and the spec-level `reconstructRowSpec` —
giving a fully spec-based discharge in row-filter terms. -/
def rowDecoderContract (raw target : ByteArray) (h rowBytes bpp : Nat) : Prop :=
  ∀ y, y < h →
    let offset := y * (rowBytes + 1)
    let filter := raw.get! offset
    let rowData := raw.extract (offset + 1) (offset + 1 + rowBytes)
    let prev :=
      if y = 0 then ByteArray.empty
      else target.extract ((y - 1) * rowBytes) (y * rowBytes)
    let slice := target.extract (y * rowBytes) ((y + 1) * rowBytes)
    ∃ (h : filter.toNat ≤ 4),
      (if filter.toNat = 0 then rowData
       else unfilterRow filter rowData prev bpp h) = slice

/-! ### Main bridge theorem -/

set_option maxHeartbeats 16000000 in
/-- The Phase 5.5 bridge: under the per-row decoder contract,
`decodeRowsLoopCore`'s same-`bpp` branch returns the target pixel
buffer.

The proof structure mirrors `decodeRowsLoopCore_encodeRaw`
(`EncodeDecodeBase.lean`), but the encoder-specific row-extract fact
is replaced by the contract hypothesis, making the lemma work for any
byte stream — including arbitrary RFC 2083 §6.2 filter combinations. -/
theorem decodeRowsLoopCore_eq_of_rowDecoderContract
    (raw target : ByteArray) (w h bpp rowBytes : Nat)
    (convert : ByteArray → Nat → Nat → Nat → ByteArray → ByteArray)
    (hLayout : raw.size = h * (rowBytes + 1))
    (hTarget : target.size = h * rowBytes)
    (hContract : rowDecoderContract raw target h rowBytes bpp) :
    decodeRowsLoopCore raw w h bpp rowBytes bpp convert 0 0 ByteArray.empty
        (ByteArray.mk <| Array.replicate (h * rowBytes) 0) =
      some target := by
  let loop := decodeRowsLoopCore raw w h bpp rowBytes bpp convert
  let pixels0 := ByteArray.mk <| Array.replicate (h * rowBytes) 0
  have hpixels0 : pixels0.size = h * rowBytes := by
    simp [pixels0, ByteArray.size, Array.size_replicate]
  -- prevAt y: the previous-row reconstruction passed into iteration y.
  let prevAt : Nat → ByteArray := fun y =>
    if y = 0 then ByteArray.empty
    else target.extract ((y - 1) * rowBytes) (y * rowBytes)
  -- The inductive invariant.
  have hk :
      ∀ k, ∀ y offset pixels,
        h - y = k →
        offset = y * (rowBytes + 1) →
        pixels.size = h * rowBytes →
        pixels.extract 0 (y * rowBytes) = target.extract 0 (y * rowBytes) →
        loop y offset (prevAt y) pixels = some target := by
    intro k
    induction k with
    | zero =>
        intro y offset pixels hk hoff hpix hprefix
        have hy : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < h := not_lt_of_ge hy
        have hsize : pixels.size = target.size := by
          simpa [hTarget] using hpix
        have hle : pixels.size ≤ y * rowBytes := by
          have hmul : h * rowBytes ≤ y * rowBytes :=
            Nat.mul_le_mul_right rowBytes hy
          simpa [hpix] using hmul
        have hprefix' :
            pixels.extract 0 pixels.size = target.extract 0 pixels.size := by
          have hpre :=
            byteArray_extract_eq_of_prefix_eq
              (a := pixels) (b := target) (n := y * rowBytes) (i := 0) (j := pixels.size)
              hprefix (by simpa [hsize] using hle)
          simpa using hpre
        have hpix_eq : pixels = target := by
          have hpix0 : pixels.extract 0 pixels.size = pixels := by
            simp [ByteArray.extract_zero_size]
          have htarget0 : target.extract 0 pixels.size = target := by
            have htarget0' : target.extract 0 target.size = target := by
              simp [ByteArray.extract_zero_size]
            simp [hsize, htarget0']
          simpa [hpix0, htarget0] using hprefix'
        simp [loop, decodeRowsLoopCore, hlt, hpix_eq]
    | succ k ih =>
        intro y offset pixels hk hoff hpix hprefix
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        have hofflt : offset < raw.size := by
          have hmul : y * (rowBytes + 1) < h * (rowBytes + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (by omega)
          simpa [hoff, hLayout] using hmul
        let rowData := raw.extract (offset + 1) (offset + 1 + rowBytes)
        have hdest : offset + 1 + rowBytes ≤ raw.size := by
          have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
            Nat.mul_le_mul_right (rowBytes + 1) hy
          have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
            simpa [hLayout] using hmul
          have hcalc : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
            calc
              offset + 1 + rowBytes = y * (rowBytes + 1) + (rowBytes + 1) := by
                simp [hoff, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              _ = (y + 1) * (rowBytes + 1) := by
                simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
          simpa [hcalc] using hmul'
        have hrowDataSize : rowData.size = rowBytes := by
          simp [rowData, ByteArray.size_extract, Nat.min_eq_left hdest]
        have hdestPix : y * rowBytes + rowBytes ≤ pixels.size := by
          have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
            Nat.mul_le_mul_right rowBytes hy
          have hmul' : (y + 1) * rowBytes ≤ pixels.size := by
            simpa [hpix] using hmul
          simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
        -- Apply the contract for row y.
        have hContractY := hContract y hlt
        rcases hContractY with ⟨hfilter, hRow⟩
        have hfilter_raw : (raw.get! offset).toNat ≤ 4 := by
          simpa [hoff] using hfilter
        -- The runtime's reconstructed row for iteration y.
        let runtimeRow :=
          if (raw.get! offset).toNat = 0 then rowData
          else unfilterRow (raw.get! offset) rowData (prevAt y) bpp hfilter_raw
        -- The contract's slice equals runtimeRow.
        have hRuntimeRow : runtimeRow = target.extract (y * rowBytes) ((y + 1) * rowBytes) := by
          have hPrev : (prevAt y : ByteArray) =
              if y = 0 then ByteArray.empty
              else target.extract ((y - 1) * rowBytes) (y * rowBytes) := rfl
          simpa [runtimeRow, rowData, hoff, hPrev] using hRow
        -- copySlice the row into pixels at offset y * rowBytes.
        let rowOffset := y * rowBytes
        let pixels' := runtimeRow.copySlice 0 pixels rowOffset rowBytes
        have htargetLe : (y + 1) * rowBytes ≤ target.size := by
          rw [hTarget]
          exact Nat.mul_le_mul_right rowBytes hy
        have hRuntimeRowSize : runtimeRow.size = rowBytes := by
          rw [hRuntimeRow]
          simp [ByteArray.size_extract]
          have hub : min ((y + 1) * rowBytes) target.size = (y + 1) * rowBytes :=
            Nat.min_eq_left htargetLe
          rw [hub]
          have hexpand : (y + 1) * rowBytes = y * rowBytes + rowBytes := by
            simp [Nat.add_mul, Nat.one_mul]
          rw [hexpand]
          omega
        have hmid :
            pixels'.extract rowOffset (rowOffset + rowBytes) =
              target.extract (y * rowBytes) ((y + 1) * rowBytes) := by
          have hsrc : 0 + rowBytes ≤ runtimeRow.size := by simp [hRuntimeRowSize]
          have hdestP : rowOffset + rowBytes ≤ pixels.size := hdestPix
          have hrowZero : runtimeRow.extract 0 rowBytes = runtimeRow := by
            have hsize : runtimeRow.size = rowBytes := hRuntimeRowSize
            have hzero :
                runtimeRow.extract 0 runtimeRow.size = runtimeRow := by
              simp [ByteArray.extract_zero_size]
            simpa [hsize] using hzero
          calc
            pixels'.extract rowOffset (rowOffset + rowBytes) =
                runtimeRow.extract 0 rowBytes := by
                  simpa [pixels', rowOffset] using
                    byteArray_copySlice_extract_mid (src := runtimeRow) (dest := pixels)
                      (srcOff := 0) (destOff := rowOffset) (len := rowBytes) hsrc hdestP
            _ = runtimeRow := hrowZero
            _ = target.extract (y * rowBytes) ((y + 1) * rowBytes) := hRuntimeRow
        have hpre' :
            pixels'.extract 0 rowOffset = pixels.extract 0 rowOffset := by
          have hdestP : rowOffset + rowBytes ≤ pixels.size := hdestPix
          simpa [pixels', rowOffset] using
            byteArray_copySlice_extract_prefix (src := runtimeRow) (dest := pixels)
              (srcOff := 0) (destOff := rowOffset) (len := rowBytes) hdestP
        have hpixSize' : pixels'.size = pixels.size := by
          have hsrc : 0 + rowBytes ≤ runtimeRow.size := by simp [hRuntimeRowSize]
          have hdestP : rowOffset + rowBytes ≤ pixels.size := hdestPix
          simpa [pixels'] using
            byteArray_copySlice_size (src := runtimeRow) (dest := pixels)
              (srcOff := 0) (destOff := rowOffset) (len := rowBytes) hsrc hdestP
        have hRowOffsetEq : rowOffset + rowBytes = (y + 1) * rowBytes := by
          simp [rowOffset, Nat.add_mul, Nat.one_mul]
        have hmid_aligned :
            pixels'.extract rowOffset ((y + 1) * rowBytes) =
              target.extract rowOffset ((y + 1) * rowBytes) := by
          have hRewrite : pixels'.extract rowOffset ((y + 1) * rowBytes) =
              pixels'.extract rowOffset (rowOffset + rowBytes) := by
            rw [hRowOffsetEq]
          rw [hRewrite, hmid]
        have hprefix' :
            pixels'.extract 0 ((y + 1) * rowBytes) =
              target.extract 0 ((y + 1) * rowBytes) := by
          have hnm : rowOffset ≤ (y + 1) * rowBytes := by
            rw [← hRowOffsetEq]; omega
          have ha : (y + 1) * rowBytes ≤ pixels'.size := by
            rw [← hRowOffsetEq]
            simpa [hpixSize'] using hdestPix
          have hb : (y + 1) * rowBytes ≤ target.size := by
            rw [hTarget]
            exact Nat.mul_le_mul_right rowBytes hy
          have hpref :
              pixels'.extract 0 rowOffset = target.extract 0 rowOffset := by
            simpa [rowOffset] using hpre'.trans hprefix
          exact
            byteArray_extract_prefix_extend (a := pixels') (b := target) (n := rowOffset)
              (m := (y + 1) * rowBytes) hnm ha hb hpref hmid_aligned
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have hoff' : offset + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
          calc
            offset + 1 + rowBytes = y * (rowBytes + 1) + (rowBytes + 1) := by
              simp [hoff, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            _ = (y + 1) * (rowBytes + 1) := by
              simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
        have hpix' : pixels'.size = h * rowBytes := by
          simpa [hpix] using hpixSize'
        -- The runtime's prevRow at iteration (y+1) is `runtimeRow`, which equals
        -- `target.extract (y * rowBytes) ((y + 1) * rowBytes) = prevAt (y + 1)`.
        have hPrevNext : prevAt (y + 1) = runtimeRow := by
          show (if y + 1 = 0 then ByteArray.empty
            else target.extract ((y + 1 - 1) * rowBytes) ((y + 1) * rowBytes)) = runtimeRow
          have hne : y + 1 ≠ 0 := by omega
          simp [hne, hRuntimeRow]
        have hnext :
            loop (y + 1) (offset + 1 + rowBytes) (prevAt (y + 1)) pixels' =
              some target :=
          ih (y := y + 1) (offset := offset + 1 + rowBytes) (pixels := pixels')
            hk' hoff' hpix' hprefix'
        have hgoal :
            loop y offset (prevAt y) pixels =
              loop (y + 1) (offset + 1 + rowBytes) runtimeRow pixels' := by
          dsimp [loop]
          rw [decodeRowsLoopCore.eq_1]
          simp [hlt, hfilter_raw, rowData, rowOffset, pixels', runtimeRow]
        rw [hgoal]
        rw [← hPrevNext]
        exact hnext
  have hstart :=
    hk (h - 0) (y := 0) (offset := 0) (pixels := pixels0)
      rfl (by simp) hpixels0 (by simp)
  -- prevAt 0 = empty.
  have hPrev0 : prevAt 0 = ByteArray.empty := by simp [prevAt]
  simpa [hPrev0] using hstart

end Lemmas

end Bitmaps
