import Bitmap.Png
import Bitmap.Lemmas.Png.CoreByteArray

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Adam7 helper facts

These lemmas document the runtime Adam7 geometry helpers added for interlaced
PNG decoding. They intentionally stop at focused helper coverage: the full
container/zlib/pixel decoder theorem remains outside this branch. -/

/-- Adam7 always consists of the seven RFC-defined passes.
This fixes the runtime pass table shape for downstream decoding arguments. -/
@[simp] lemma adam7Passes_length : adam7Passes.length = 7 := by
  rfl

/-- A pass with a start coordinate outside the image has zero samples.
This is the empty-pass case used by small Adam7 images. -/
lemma adam7PassDim_eq_zero_of_le {full start step : Nat} (hstart : full ≤ start) :
    adam7PassDim full start step = 0 := by
  unfold adam7PassDim
  simp [Nat.not_lt.mpr hstart]

/-- If a pass starts inside the image, its dimension is positive.
This separates real pass rows from empty Adam7 passes. -/
lemma adam7PassDim_pos_of_lt {full start step : Nat} (hstart : start < full) :
    0 < adam7PassDim full start step := by
  unfold adam7PassDim
  simp [hstart]

/-- Pass-local coordinates map back inside the full image dimension.
This is the core bound needed when scattering pass pixels into the flat image. -/
lemma adam7PassCoord_lt_full {full start step i : Nat}
    (hi : i < adam7PassDim full start step) :
    start + i * step < full := by
  unfold adam7PassDim at hi
  by_cases hstart : start < full
  · simp [hstart] at hi
    have hiLe : i ≤ (full - 1 - start) / step := Nat.lt_succ_iff.mp hi
    have hmul : i * step ≤ ((full - 1 - start) / step) * step :=
      Nat.mul_le_mul_right step hiLe
    have hdiv : ((full - 1 - start) / step) * step ≤ full - 1 - start :=
      Nat.div_mul_le_self _ _
    have hle : i * step ≤ full - 1 - start := le_trans hmul hdiv
    omega
  · simp [hstart] at hi

/-- Converting a flat pixel buffer into filter-0 row format preserves the
destination buffer size at every recursive step. -/
lemma adam7FlatToRawLoop_size (flat : ByteArray) (rowBytes h y : Nat) (raw : ByteArray)
    (hflat : flat.size = h * rowBytes) (hraw : raw.size = h * (rowBytes + 1)) :
    (adam7FlatToRawLoop flat rowBytes h y raw).size = raw.size := by
  have hk :
      ∀ k, ∀ y raw, h - y = k → raw.size = h * (rowBytes + 1) →
        (adam7FlatToRawLoop flat rowBytes h y raw).size = raw.size := by
    intro k
    induction k with
    | zero =>
        intro y raw hk hraw
        have hy : h ≤ y := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ y < h := not_lt_of_ge hy
        simp [adam7FlatToRawLoop, hlt, hraw]
    | succ k ih =>
        intro y raw hk hraw
        have hlt : y < h := Nat.lt_of_sub_eq_succ hk
        have hy : y + 1 ≤ h := Nat.succ_le_of_lt hlt
        have hsrc : y * rowBytes + rowBytes ≤ flat.size := by
          have hmul : (y + 1) * rowBytes ≤ h * rowBytes :=
            Nat.mul_le_mul_right rowBytes hy
          have hmul' : (y + 1) * rowBytes ≤ flat.size := by
            simpa [hflat] using hmul
          simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm] using hmul'
        have hdest : y * (rowBytes + 1) + 1 + rowBytes ≤ raw.size := by
          have hmul : (y + 1) * (rowBytes + 1) ≤ h * (rowBytes + 1) :=
            Nat.mul_le_mul_right (rowBytes + 1) hy
          have hmul' : (y + 1) * (rowBytes + 1) ≤ raw.size := by
            simpa [hraw] using hmul
          have hcalc : y * (rowBytes + 1) + 1 + rowBytes = (y + 1) * (rowBytes + 1) := by
            calc
              y * (rowBytes + 1) + 1 + rowBytes =
                  y * (rowBytes + 1) + (rowBytes + 1) := by
                    omega
              _ = (y + 1) * (rowBytes + 1) := by
                    simp [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm]
          simpa [hcalc] using hmul'
        let raw' :=
          flat.copySlice (y * rowBytes) raw (y * (rowBytes + 1) + 1) rowBytes
        have hcopy : raw'.size = raw.size := by
          exact
            byteArray_copySlice_size (src := flat) (dest := raw)
              (srcOff := y * rowBytes) (destOff := y * (rowBytes + 1) + 1) (len := rowBytes)
              hsrc hdest
        have hk' : h - (y + 1) = k := by
          have hsum : h = Nat.succ k + y := Nat.eq_add_of_sub_eq (Nat.le_of_lt hlt) hk
          calc
            h - (y + 1) = (Nat.succ k + y) - (y + 1) := by simp [hsum]
            _ = k := by omega
        have hraw' : raw'.size = h * (rowBytes + 1) := by
          calc
            raw'.size = raw.size := hcopy
            _ = h * (rowBytes + 1) := hraw
        have ih' :=
          ih (y := y + 1) (raw := raw') hk' hraw'
        have hdef :
            (adam7FlatToRawLoop flat rowBytes h y raw).size =
              (if y < h then adam7FlatToRawLoop flat rowBytes h (y + 1) raw' else raw).size := by
          have hdef0 :=
            congrArg ByteArray.size
              (adam7FlatToRawLoop.eq_1 (flat := flat) (rowBytes := rowBytes)
                (h := h) (y := y) (raw := raw))
          simpa [raw'] using hdef0
        calc
          (adam7FlatToRawLoop flat rowBytes h y raw).size =
              (if y < h then adam7FlatToRawLoop flat rowBytes h (y + 1) raw' else raw).size := by
                rw [hdef]
          _ = (adam7FlatToRawLoop flat rowBytes h (y + 1) raw').size := by
                simp [hlt]
          _ = raw'.size := ih'
          _ = raw.size := hcopy
  exact hk (h - y) y raw rfl hraw

/-- Adam7 normalization produces the same byte count as ordinary filter-0 PNG
rows: one filter byte plus one full row of pixel bytes per image row. -/
lemma adam7FlatToFilterZeroRaw_size (flat : ByteArray) (w h bpp : Nat)
    (hflat : flat.size = h * (w * bpp)) :
    (adam7FlatToFilterZeroRaw flat w h bpp).size = h * (w * bpp + 1) := by
  let rowBytes := w * bpp
  let rawSize := h * (rowBytes + 1)
  have hraw : (ByteArray.mk (Array.replicate rawSize 0)).size = h * (rowBytes + 1) := by
    simp [rawSize, ByteArray.size, Array.size_replicate]
  unfold adam7FlatToFilterZeroRaw
  have hsize :=
    adam7FlatToRawLoop_size (flat := flat) (rowBytes := rowBytes) (h := h) (y := 0)
      (raw := ByteArray.mk (Array.replicate rawSize 0)) hflat hraw
  calc
    (adam7FlatToRawLoop flat rowBytes h 0
        (ByteArray.mk (Array.replicate rawSize 0))).size =
        (ByteArray.mk (Array.replicate rawSize 0)).size := hsize
    _ = h * (w * bpp + 1) := by
          simp [rawSize, rowBytes, ByteArray.size, Array.size_replicate]

/-- Non-interlaced images bypass Adam7 normalization unchanged.
This keeps the existing encoder round-trip proof on the old row layout. -/
@[simp] lemma normalizeRawByInterlace_zero (raw : ByteArray) (hdr : PngHeader) (bpp : Nat)
    (hinterlace : hdr.interlace = 0) :
    normalizeRawByInterlace? raw hdr bpp = some raw := by
  simp [normalizeRawByInterlace?, hinterlace]

end Lemmas

end Bitmaps
