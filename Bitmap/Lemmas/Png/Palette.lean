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

/-- Palette transparency metadata exposes its alpha byte payload unchanged.
This pins the handoff from parsed `tRNS` metadata into palette expansion. -/
@[simp] lemma paletteAlphaBytes?_paletteAlpha (alpha : ByteArray) :
    paletteAlphaBytes? { PngMetadata.empty with transparency := some (.paletteAlpha alpha) } =
      some alpha := by
  simp [paletteAlphaBytes?]

/-- Without palette `tRNS`, every palette entry is treated as fully opaque.
This records the decoder's default-alpha rule for indexed PNGs. -/
@[simp] lemma paletteAlphaAt_none (idx : Nat) :
    paletteAlphaAt none idx = 0xff := by
  rfl

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
