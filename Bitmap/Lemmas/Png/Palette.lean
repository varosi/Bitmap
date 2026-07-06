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

/-- Packing one indexed sample into a row does not change the row byte count.
This is the inner-loop invariant for indexed row construction. -/
lemma palettePackIndexIntoRow_size (row : ByteArray) (bitDepth x : Nat) (idx : UInt8) :
    (palettePackIndexIntoRow row bitDepth x idx).size = row.size := by
  unfold palettePackIndexIntoRow
  by_cases h8 : bitDepth == 8
  · simp [h8, byteArray_size_set!]
  · simp [h8, byteArray_size_set!]

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
  simpa [rowBytes] using
    encodeIndexedPackedRowsLoop_size (bmp := bmp) (rowBytes := rowBytes)
      (y := 0) (packed := ByteArray.empty) (Nat.zero_le _) (by simp)

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
  simpa [rowBytes] using
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

end Lemmas

end Bitmaps
