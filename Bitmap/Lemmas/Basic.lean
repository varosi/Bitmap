import Bitmap.Basic
import Bitmap.Lemmas.BasicU16
import Init.Data.Nat.Lemmas

universe u

namespace Bitmaps

namespace Lemmas

class LawfulChannelFormat (RangeT : Type u) [ChannelFormat RangeT] : Prop where
  toNat_natCast_of_le_max :
    ∀ n : Nat, n ≤ ChannelFormat.maxValue (RangeT := RangeT) →
      ChannelFormat.toNat (Nat.cast (R := RangeT) n) = n
  natCast_toNat : ∀ x : RangeT,
      (Nat.cast (R := RangeT) (ChannelFormat.toNat x)) = x
  toNat_le_max : ∀ x : RangeT,
      ChannelFormat.toNat x ≤ ChannelFormat.maxValue (RangeT := RangeT)
  maxValue_pos : 0 < ChannelFormat.maxValue (RangeT := RangeT)
  read_write :
    ∀ (data : ByteArray) (base : Nat)
      (h : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
      (x : RangeT),
      ChannelFormat.read (ChannelFormat.write data base h x) base
        (by
          simpa [ChannelFormat.write_size
            (data := data) (base := base) (h := h) (x := x)] using h) = x
  read_write_preserve :
    ∀ (data : ByteArray) (readBase writeBase : Nat)
      (hread : readBase + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
      (hwrite : writeBase + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
      (x : RangeT),
      readBase + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < writeBase ∨
        writeBase + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < readBase →
      ChannelFormat.read (ChannelFormat.write data writeBase hwrite x) readBase
        (by
          simpa [ChannelFormat.write_size
            (data := data) (base := writeBase) (h := hwrite) (x := x)] using hread) =
        ChannelFormat.read data readBase hread

instance : LawfulChannelFormat UInt8 where
  toNat_natCast_of_le_max := by
    intro n hn
    have hn' : n ≤ 255 := by
      change n ≤ 255 at hn
      exact hn
    have hlt : n < 2 ^ 8 := by omega
    change UInt8.toNat (UInt8.ofNat n) = n
    rw [UInt8.toNat.eq_1]
    rw [UInt8.ofNat]
    rw [BitVec.toNat_ofNat]
    simp [Nat.mod_eq_of_lt hlt]
  natCast_toNat := by
    intro x
    change UInt8.ofNat (UInt8.toNat x) = x
    simp
  toNat_le_max := by
    intro x
    have hlt : UInt8.toNat x < UInt8.size := by
      rw [UInt8.toNat.eq_1]
      exact x.toBitVec.isLt
    have hlt' : UInt8.toNat x < 256 := by simpa using hlt
    change UInt8.toNat x ≤ 255
    exact Nat.le_of_lt_succ hlt'
  maxValue_pos := by decide
  read_write := by
    intro data base h x
    change (data.set base x (by omega)).get base _ = x
    cases data with
    | mk arr =>
        simp [ByteArray.set, ByteArray.get]
  read_write_preserve := by
    intro data readBase writeBase hread hwrite x hdisj
    have hread' : readBase < data.size := by omega
    have hwrite' : writeBase < data.size := by omega
    have hreadAfter : readBase < (data.set writeBase x hwrite').size := by
      simpa [byteArray_set_size (bs := data) (i := writeBase) (hi := hwrite') (v := x)]
        using hread'
    have hne : writeBase ≠ readBase := by
      rcases hdisj with h | h <;> omega
    simpa [ChannelFormat.read, ChannelFormat.write] using
      (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase)
        (hi := hwrite') (hj := hread') (hij := hne) (v := x) (h' := hreadAfter))

instance : LawfulChannelFormat UInt16 where
  toNat_natCast_of_le_max := by
    intro n hn
    have hn' : n ≤ 65535 := by
      change n ≤ 65535 at hn
      exact hn
    have hlt : n < 2 ^ 16 := by omega
    change UInt16.toNat (UInt16.ofNat n) = n
    rw [UInt16.toNat.eq_1]
    rw [UInt16.ofNat]
    rw [BitVec.toNat_ofNat]
    simp [Nat.mod_eq_of_lt hlt]
  natCast_toNat := by
    intro x
    change UInt16.ofNat (UInt16.toNat x) = x
    simp
  toNat_le_max := by
    intro x
    have hlt : UInt16.toNat x < UInt16.size := by
      rw [UInt16.toNat.eq_1]
      exact x.toBitVec.isLt
    have hlt' : UInt16.toNat x < 65536 := by simpa using hlt
    change UInt16.toNat x ≤ 65535
    exact Nat.le_of_lt_succ hlt'
  maxValue_pos := by decide
  read_write := by
    intro data base h x
    simpa [ChannelFormat.read, ChannelFormat.write] using readU16BEAt_write_same data base (by omega) x
  read_write_preserve := by
    intro data readBase writeBase hread hwrite x hdisj
    rcases hdisj with hbefore | hbefore
    · simpa [ChannelFormat.read, ChannelFormat.write] using
        (readU16BEAt_write_after data readBase writeBase
          (by omega) (by omega) x (by omega))
    · simpa [ChannelFormat.read, ChannelFormat.write] using
        (readU16BEAt_write_before data readBase writeBase
          (by omega) (by omega) x (by omega))

/-- Proof-side round-trip law for pixel byte formats.
It keeps `Bitmap.Basic` focused on executable layout data and size preservation. -/
class LawfulPixelFormat (α : Type u) [PixelFormat α] : Prop where
  read_write :
    ∀ (data : ByteArray) (base : Nat)
      (h : base + (PixelFormat.bytesPerPixel (α := α) - 1) < data.size) (px : α),
      PixelFormat.read (PixelFormat.write data base h px) base
        (by
          simpa [PixelFormat.write_size
            (data := data) (base := base) (h := h) (px := px)] using h) = px

namespace ChannelLayout

/-- One-channel layouts read back the value most recently written at the same base. -/
theorem read_write1 {RangeT α : Type u} [ChannelFormat RangeT] [LawfulChannelFormat RangeT]
    (mk : RangeT → α) (get0 : α → RangeT)
    (eta : ∀ px : α, mk (get0 px) = px)
    (data : ByteArray) (base : Nat)
    (h : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    ChannelLayout.read1 mk (ChannelLayout.write1 get0 data base h px) base
      (by
        have hsize := ChannelLayout.write1_size get0 data base h px
        simpa [hsize] using h) = px := by
  unfold ChannelLayout.read1 ChannelLayout.write1
  rw [LawfulChannelFormat.read_write]
  exact eta px

/-- Two-channel layouts read back both values most recently written at the same base. -/
theorem read_write2 {RangeT α : Type u} [ChannelFormat RangeT] [LawfulChannelFormat RangeT]
    (mk : RangeT → RangeT → α) (get0 get1 : α → RangeT)
    (eta : ∀ px : α, mk (get0 px) (get1 px) = px)
    (data : ByteArray) (base : Nat)
    (h : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    ChannelLayout.read2 mk (ChannelLayout.write2 get0 get1 data base h px) base
      (by
        have hsize := ChannelLayout.write2_size get0 get1 data base h px
        simpa [hsize] using h) = px := by
  unfold ChannelLayout.read2 ChannelLayout.write2
  have h0 := ChannelLayout.bound2_0 (RangeT := RangeT) h
  let data1 := ChannelFormat.write data base h0 (get0 px)
  have hsize1 : data1.size = data.size :=
    ChannelFormat.write_size data base h0 (get0 px)
  have h1 : base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data1.size := by
    simpa [hsize1] using ChannelLayout.bound2_1 (RangeT := RangeT) h
  let data2 := ChannelFormat.write data1
    (base + ChannelFormat.byteSize (RangeT := RangeT)) h1 (get1 px)
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size :=
      ChannelFormat.write_size data1
        (base + ChannelFormat.byteSize (RangeT := RangeT)) h1 (get1 px)
    simpa [hsize1] using hsize2'
  have h0d1 : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data1.size := by
    simpa [hsize1] using h0
  have h0d2 : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data2.size := by
    simpa [hsize2] using h0
  have h1d2 : base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data2.size := by
    simpa [hsize2] using ChannelLayout.bound2_1 (RangeT := RangeT) h
  have hread0 : ChannelFormat.read data2 base h0d2 = get0 px := by
    have hkeep : ChannelFormat.read data2 base h0d2 =
        ChannelFormat.read data1 base h0d1 := by
      have hdisj :
          base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) <
            base + ChannelFormat.byteSize (RangeT := RangeT) := by
        have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
        omega
      simpa [data2] using
        (LawfulChannelFormat.read_write_preserve data1 base
          (base + ChannelFormat.byteSize (RangeT := RangeT)) h0d1 h1 (get1 px)
          (Or.inl hdisj))
    have hsame : ChannelFormat.read data1 base h0d1 = get0 px := by
      simpa [data1] using LawfulChannelFormat.read_write data base h0 (get0 px)
    simp [hkeep, hsame]
  have hread1 : ChannelFormat.read data2
      (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d2 = get1 px := by
    simpa [data2] using
      LawfulChannelFormat.read_write data1
        (base + ChannelFormat.byteSize (RangeT := RangeT)) h1 (get1 px)
  simpa [data1, data2, hread0, hread1] using eta px

/-- Three-channel layouts read back all values most recently written at the same base. -/
theorem read_write3 {RangeT α : Type u} [ChannelFormat RangeT] [LawfulChannelFormat RangeT]
    (mk : RangeT → RangeT → RangeT → α) (get0 get1 get2 : α → RangeT)
    (eta : ∀ px : α, mk (get0 px) (get1 px) (get2 px) = px)
    (data : ByteArray) (base : Nat)
    (h : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    ChannelLayout.read3 mk (ChannelLayout.write3 get0 get1 get2 data base h px) base
      (by
        have hsize := ChannelLayout.write3_size get0 get1 get2 data base h px
        simpa [hsize] using h) = px := by
  unfold ChannelLayout.read3 ChannelLayout.write3
  have h01 : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
    have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
    omega
  let data2 := ChannelLayout.write2 get0 get1 data base h01 px
  have hsize2 : data2.size = data.size :=
    ChannelLayout.write2_size get0 get1 data base h01 px
  have h2 : base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data2.size := by
    simpa [hsize2] using ChannelLayout.bound3_2 (RangeT := RangeT) h
  let data3 := ChannelFormat.write data2
    (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2 (get2 px)
  have hsize3 : data3.size = data.size := by
    have hsize3' : data3.size = data2.size :=
      ChannelFormat.write_size data2
        (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2 (get2 px)
    simpa [hsize2] using hsize3'
  have h0d2 : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data2.size := by
    simpa [hsize2] using ChannelLayout.bound3_0 (RangeT := RangeT) h
  have h1d2 : base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data2.size := by
    simpa [hsize2] using ChannelLayout.bound3_1 (RangeT := RangeT) h
  have h0d3 : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using ChannelLayout.bound3_0 (RangeT := RangeT) h
  have h1d3 : base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using ChannelLayout.bound3_1 (RangeT := RangeT) h
  have h2d3 : base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using ChannelLayout.bound3_2 (RangeT := RangeT) h
  have hpair := read_write2
    (RangeT := RangeT) (α := RangeT × RangeT)
    (fun x y => (x, y)) Prod.fst Prod.snd
    (by intro p; cases p; rfl)
    data base h01 (get0 px, get1 px)
  have hpair0 :
      ChannelFormat.read data2 base h0d2 = get0 px := by
    have := congrArg Prod.fst hpair
    simpa [ChannelLayout.read2, ChannelLayout.write2, data2, ChannelFormat.read, ChannelFormat.write] using this
  have hpair1 :
      ChannelFormat.read data2 (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d2 =
        get1 px := by
    have := congrArg Prod.snd hpair
    simpa [ChannelLayout.read2, ChannelLayout.write2, data2, ChannelFormat.read, ChannelFormat.write] using this
  have hread0 : ChannelFormat.read data3 base h0d3 = get0 px := by
    have hkeep : ChannelFormat.read data3 base h0d3 =
        ChannelFormat.read data2 base h0d2 := by
      have hdisj :
          base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) <
            base + 2 * ChannelFormat.byteSize (RangeT := RangeT) := by
        have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
        omega
      simpa [data3] using
        (LawfulChannelFormat.read_write_preserve data2 base
          (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h0d2 h2 (get2 px)
          (Or.inl hdisj))
    simp [hkeep, hpair0]
  have hread1 : ChannelFormat.read data3
      (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d3 = get1 px := by
    have hkeep : ChannelFormat.read data3
        (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d3 =
        ChannelFormat.read data2 (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d2 := by
      have hdisj :
          base + ChannelFormat.byteSize (RangeT := RangeT) +
              (ChannelFormat.byteSize (RangeT := RangeT) - 1) <
            base + 2 * ChannelFormat.byteSize (RangeT := RangeT) := by
        have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
        omega
      simpa [data3] using
        (LawfulChannelFormat.read_write_preserve data2
          (base + ChannelFormat.byteSize (RangeT := RangeT))
          (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h1d2 h2 (get2 px)
          (Or.inl hdisj))
    simp [hkeep, hpair1]
  have hread2 : ChannelFormat.read data3
      (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2d3 = get2 px := by
    simpa [data3] using
      LawfulChannelFormat.read_write data2
        (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2 (get2 px)
  simpa [data2, data3, hread0, hread1, hread2] using eta px

/-- Four-channel layouts read back all values most recently written at the same base. -/
theorem read_write4 {RangeT α : Type u} [ChannelFormat RangeT] [LawfulChannelFormat RangeT]
    (mk : RangeT → RangeT → RangeT → RangeT → α) (get0 get1 get2 get3 : α → RangeT)
    (eta : ∀ px : α, mk (get0 px) (get1 px) (get2 px) (get3 px) = px)
    (data : ByteArray) (base : Nat)
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    ChannelLayout.read4 mk (ChannelLayout.write4 get0 get1 get2 get3 data base h px) base
      (by
        have hsize := ChannelLayout.write4_size get0 get1 get2 get3 data base h px
        simpa [hsize] using h) = px := by
  unfold ChannelLayout.read4 ChannelLayout.write4
  have h012 : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
    have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
    omega
  let data3 := ChannelLayout.write3 get0 get1 get2 data base h012 px
  have hsize3 : data3.size = data.size :=
    ChannelLayout.write3_size get0 get1 get2 data base h012 px
  have h3 : base + 3 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using ChannelLayout.bound4_3 (RangeT := RangeT) h
  let data4 := ChannelFormat.write data3
    (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h3 (get3 px)
  have hsize4 : data4.size = data.size := by
    have hsize4' : data4.size = data3.size :=
      ChannelFormat.write_size data3
        (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h3 (get3 px)
    simpa [hsize3] using hsize4'
  have h0d3 : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using ChannelLayout.bound4_0 (RangeT := RangeT) h
  have h1d3 : base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using ChannelLayout.bound4_1 (RangeT := RangeT) h
  have h2d3 : base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using ChannelLayout.bound4_2 (RangeT := RangeT) h
  have h0d4 : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data4.size := by
    simpa [hsize4] using ChannelLayout.bound4_0 (RangeT := RangeT) h
  have h1d4 : base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data4.size := by
    simpa [hsize4] using ChannelLayout.bound4_1 (RangeT := RangeT) h
  have h2d4 : base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data4.size := by
    simpa [hsize4] using ChannelLayout.bound4_2 (RangeT := RangeT) h
  have h3d4 : base + 3 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data4.size := by
    simpa [hsize4] using ChannelLayout.bound4_3 (RangeT := RangeT) h
  have htriple := read_write3
    (RangeT := RangeT) (α := RangeT × RangeT × RangeT)
    (fun x y z => (x, y, z))
    Prod.fst (fun p => p.2.1) (fun p => p.2.2)
    (by intro p; cases p with | mk x yz => cases yz; rfl)
    data base h012 (get0 px, get1 px, get2 px)
  have hdata3 : data3 =
      ChannelLayout.write3 Prod.fst (fun p => p.2.1) (fun p => p.2.2)
        data base h012 (get0 px, get1 px, get2 px) := by
    rfl
  have htriple0 :
      ChannelFormat.read data3 base h0d3 = get0 px := by
    have := congrArg Prod.fst htriple
    simpa [hdata3, ChannelLayout.read3, ChannelFormat.read, ChannelFormat.write] using this
  have htriple1 :
      ChannelFormat.read data3 (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d3 =
        get1 px := by
    have := congrArg (fun p : RangeT × RangeT × RangeT => p.2.1) htriple
    simpa [hdata3, ChannelLayout.read3, ChannelFormat.read, ChannelFormat.write] using this
  have htriple2 :
      ChannelFormat.read data3 (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2d3 =
        get2 px := by
    have := congrArg (fun p : RangeT × RangeT × RangeT => p.2.2) htriple
    simpa [hdata3, ChannelLayout.read3, ChannelFormat.read, ChannelFormat.write] using this
  have hread0 : ChannelFormat.read data4 base h0d4 = get0 px := by
    have hkeep : ChannelFormat.read data4 base h0d4 =
        ChannelFormat.read data3 base h0d3 := by
      have hdisj :
          base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) <
            base + 3 * ChannelFormat.byteSize (RangeT := RangeT) := by
        have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
        omega
      simpa [data4] using
        (LawfulChannelFormat.read_write_preserve data3 base
          (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h0d3 h3 (get3 px)
          (Or.inl hdisj))
    simp [hkeep, htriple0]
  have hread1 : ChannelFormat.read data4
      (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d4 = get1 px := by
    have hkeep : ChannelFormat.read data4
        (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d4 =
        ChannelFormat.read data3 (base + ChannelFormat.byteSize (RangeT := RangeT)) h1d3 := by
      have hdisj :
          base + ChannelFormat.byteSize (RangeT := RangeT) +
              (ChannelFormat.byteSize (RangeT := RangeT) - 1) <
            base + 3 * ChannelFormat.byteSize (RangeT := RangeT) := by
        have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
        omega
      simpa [data4] using
        (LawfulChannelFormat.read_write_preserve data3
          (base + ChannelFormat.byteSize (RangeT := RangeT))
          (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h1d3 h3 (get3 px)
          (Or.inl hdisj))
    simp [hkeep, htriple1]
  have hread2 : ChannelFormat.read data4
      (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2d4 = get2 px := by
    have hkeep : ChannelFormat.read data4
        (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2d4 =
        ChannelFormat.read data3 (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2d3 := by
      have hdisj :
          base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
              (ChannelFormat.byteSize (RangeT := RangeT) - 1) <
            base + 3 * ChannelFormat.byteSize (RangeT := RangeT) := by
        have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
        omega
      simpa [data4] using
        (LawfulChannelFormat.read_write_preserve data3
          (base + 2 * ChannelFormat.byteSize (RangeT := RangeT))
          (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h2d3 h3 (get3 px)
          (Or.inl hdisj))
    simp [hkeep, htriple2]
  have hread3 : ChannelFormat.read data4
      (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h3d4 = get3 px := by
    simpa [data4] using
      LawfulChannelFormat.read_write data3
        (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h3 (get3 px)
  simpa [data3, data4, hread0, hread1, hread2, hread3] using eta px

end ChannelLayout

instance instLawfulPixelFormatRGB8 : LawfulPixelFormat RGB8 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatRGB8, ChannelLayout.pixelFormat3] using
        ChannelLayout.read_write3
          (RangeT := UInt8) (α := RGB8)
          (fun r g b => ({ r := r, g := g, b := b } : RGB8))
          RGB.r RGB.g RGB.b
          (by intro px; cases px; rfl)
          data base h px }

instance instLawfulPixelFormatRGBA8 : LawfulPixelFormat RGBA8 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatRGBA8, ChannelLayout.pixelFormat4] using
        ChannelLayout.read_write4
          (RangeT := UInt8) (α := RGBA8)
          (fun r g b a => ({ r := r, g := g, b := b, a := a } : RGBA8))
          RGBA.r RGBA.g RGBA.b RGBA.a
          (by intro px; cases px; rfl)
          data base h px }

instance instLawfulPixelFormatGray8 : LawfulPixelFormat Gray8 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatGray8, ChannelLayout.pixelFormat1] using
        ChannelLayout.read_write1
          (RangeT := UInt8) (α := Gray8)
          (fun v => ({ v := v } : Gray8))
          Gray.v
          (by intro px; cases px; rfl)
          data base h px }

instance instLawfulPixelFormatGrayAlpha8 : LawfulPixelFormat GrayAlpha8 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatGrayAlpha8, ChannelLayout.pixelFormat2] using
        ChannelLayout.read_write2
          (RangeT := UInt8) (α := GrayAlpha8)
          (fun v a => ({ v := v, a := a } : GrayAlpha8))
          GrayAlpha.v GrayAlpha.a
          (by intro px; cases px; rfl)
          data base h px }

instance instLawfulPixelFormatGray16 : LawfulPixelFormat Gray16 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatGray16, ChannelLayout.pixelFormat1] using
        ChannelLayout.read_write1
          (RangeT := UInt16) (α := Gray16)
          (fun v => ({ v := v } : Gray16))
          Gray.v
          (by intro px; cases px; rfl)
          data base h px }

instance instLawfulPixelFormatGrayAlpha16 : LawfulPixelFormat GrayAlpha16 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatGrayAlpha16, ChannelLayout.pixelFormat2] using
        ChannelLayout.read_write2
          (RangeT := UInt16) (α := GrayAlpha16)
          (fun v a => ({ v := v, a := a } : GrayAlpha16))
          GrayAlpha.v GrayAlpha.a
          (by intro px; cases px; rfl)
          data base h px }

instance instLawfulPixelFormatRGB16 : LawfulPixelFormat RGB16 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatRGB16, ChannelLayout.pixelFormat3] using
        ChannelLayout.read_write3
          (RangeT := UInt16) (α := RGB16)
          (fun r g b => ({ r := r, g := g, b := b } : RGB16))
          RGB.r RGB.g RGB.b
          (by intro px; cases px; rfl)
          data base h px }

instance instLawfulPixelFormatRGBA16 : LawfulPixelFormat RGBA16 :=
  { read_write := by
      intro data base h px
      simpa [instPixelFormatRGBA16, ChannelLayout.pixelFormat4] using
        ChannelLayout.read_write4
          (RangeT := UInt16) (α := RGBA16)
          (fun r g b a => ({ r := r, g := g, b := b, a := a } : RGBA16))
          RGBA.r RGBA.g RGBA.b RGBA.a
          (by intro px; cases px; rfl)
          data base h px }

/-- `Alpha.divRound` returns `0` when its numerator is `0`. -/
lemma alphaDivRound_zero_left (den : Nat) : Alpha.divRound 0 den = 0 := by
  cases den with
  | zero => simp [Alpha.divRound]
  | succ d =>
      have hlt : Nat.succ d / 2 < Nat.succ d :=
        Nat.div_lt_self (Nat.succ_pos d) (by decide : 1 < (2 : Nat))
      unfold Alpha.divRound
      simp [Nat.div_eq_of_lt hlt]

/-- `Alpha.divRound (x * den) den = x` for positive `den`. -/
lemma alphaDivRound_mul_right (x den : Nat) (hden : 0 < den) :
    Alpha.divRound (x * den) den = x := by
  unfold Alpha.divRound
  have hden' : den ≠ 0 := Nat.ne_of_gt hden
  simp [hden']
  have hhalf_lt : den / 2 < den := by
    exact Nat.div_lt_self hden (by decide : 1 < (2 : Nat))
  have hhalf_zero : (den / 2) / den = 0 := Nat.div_eq_of_lt hhalf_lt
  calc
    (x * den + den / 2) / den
        = (den * x + den / 2) / den := by simp [Nat.mul_comm]
    _ = x + (den / 2) / den := by
          exact Nat.mul_add_div hden x (den / 2)
    _ = x := by simp [hhalf_zero]

/-- `Alpha.clamp` converts back to `Nat` as `min maxValue n`. -/
lemma alphaClamp_toNat_eq_min {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (n : Nat) :
    ChannelFormat.toNat (Alpha.clamp (RangeT := RangeT) n) =
      Nat.min (ChannelFormat.maxValue (RangeT := RangeT)) n := by
  unfold Alpha.clamp
  exact LawfulChannelFormat.toNat_natCast_of_le_max
    (RangeT := RangeT)
    (Nat.min (ChannelFormat.maxValue (RangeT := RangeT)) n)
    (Nat.min_le_left _ _)

/-- `Alpha.clamp` is a left inverse of `toNat` on channel values. -/
lemma alphaClamp_toNat_self {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (x : RangeT) :
    Alpha.clamp (RangeT := RangeT) (ChannelFormat.toNat x) = x := by
  unfold Alpha.clamp
  have hle : ChannelFormat.toNat x ≤ ChannelFormat.maxValue (RangeT := RangeT) :=
    LawfulChannelFormat.toNat_le_max (RangeT := RangeT) x
  have hmin : Nat.min (ChannelFormat.maxValue (RangeT := RangeT)) (ChannelFormat.toNat x) =
      ChannelFormat.toNat x := by
    exact Nat.min_eq_right hle
  simpa [hmin] using (LawfulChannelFormat.natCast_toNat (RangeT := RangeT) x)

/-- `Alpha.over dst 0 = dst`. -/
lemma alphaOver_src_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dstA : RangeT) :
    Alpha.over (RangeT := RangeT) dstA (Nat.cast (R := RangeT) 0) = dstA := by
  unfold Alpha.over
  have hsrc0 : ChannelFormat.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  simp [hsrc0, alphaDivRound_mul_right, LawfulChannelFormat.maxValue_pos]
  exact alphaClamp_toNat_self (RangeT := RangeT) dstA

/-- `Alpha.over 0 src = src`. -/
lemma alphaOver_dst_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (srcA : RangeT) :
    Alpha.over (RangeT := RangeT) (Nat.cast (R := RangeT) 0) srcA = srcA := by
  unfold Alpha.over
  have hdst0 : ChannelFormat.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  simp [hdst0, alphaDivRound_zero_left]
  exact alphaClamp_toNat_self (RangeT := RangeT) srcA

/-- `Alpha.over dst max = max`. -/
lemma alphaOver_src_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dstA : RangeT) :
    Alpha.over (RangeT := RangeT) dstA
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  unfold Alpha.over
  have hsrcMax : ChannelFormat.toNat
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) =
      ChannelFormat.maxValue (RangeT := RangeT) := by
    exact LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT)
      (ChannelFormat.maxValue (RangeT := RangeT)) (Nat.le_refl _)
  simp [hsrcMax, alphaDivRound_zero_left]
  unfold Alpha.clamp
  simp

/-- The `Nat` value of `Alpha.clamp n` is bounded by `maxValue`. -/
lemma alphaClamp_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (n : Nat) :
    ChannelFormat.toNat (Alpha.clamp (RangeT := RangeT) n) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  rw [alphaClamp_toNat_eq_min (RangeT := RangeT) n]
  exact Nat.min_le_left _ _

/-- `Alpha.clamp` is idempotent after converting through `toNat`. -/
lemma alphaClamp_idempotent {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (n : Nat) :
    Alpha.clamp (RangeT := RangeT)
      (ChannelFormat.toNat (Alpha.clamp (RangeT := RangeT) n)) =
      Alpha.clamp (RangeT := RangeT) n := by
  exact alphaClamp_toNat_self (RangeT := RangeT) (Alpha.clamp (RangeT := RangeT) n)

/-- `Alpha.mulNorm` is commutative. -/
lemma alphaMulNorm_comm {RangeT : Type u} [ChannelFormat RangeT]
    (x y : RangeT) :
    Alpha.mulNorm (RangeT := RangeT) x y = Alpha.mulNorm (RangeT := RangeT) y x := by
  unfold Alpha.mulNorm
  simp [Nat.mul_comm]

/-- Characterizes `toNat (Alpha.mulNorm x y)` as a clamped rounded product. -/
lemma alphaMulNorm_toNat_eq_min {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (x y : RangeT) :
    ChannelFormat.toNat (Alpha.mulNorm (RangeT := RangeT) x y) =
      Nat.min (ChannelFormat.maxValue (RangeT := RangeT))
        (Alpha.divRound (ChannelFormat.toNat x * ChannelFormat.toNat y)
          (ChannelFormat.maxValue (RangeT := RangeT))) := by
  unfold Alpha.mulNorm
  exact alphaClamp_toNat_eq_min (RangeT := RangeT) _

/-- The `Nat` value of `Alpha.mulNorm x y` is bounded by `maxValue`. -/
lemma alphaMulNorm_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (x y : RangeT) :
    ChannelFormat.toNat (Alpha.mulNorm (RangeT := RangeT) x y) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  rw [alphaMulNorm_toNat_eq_min (RangeT := RangeT) x y]
  exact Nat.min_le_left _ _

/-- `Alpha.mulNorm 0 y = 0`. -/
lemma alphaMulNorm_zero_left {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (y : RangeT) :
    Alpha.mulNorm (RangeT := RangeT) (Nat.cast (R := RangeT) 0) y =
      Nat.cast (R := RangeT) 0 := by
  have h0 : ChannelFormat.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  unfold Alpha.mulNorm
  unfold Alpha.clamp
  simp [h0, alphaDivRound_zero_left]

/-- `Alpha.mulNorm x 0 = 0`. -/
lemma alphaMulNorm_zero_right {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (x : RangeT) :
    Alpha.mulNorm (RangeT := RangeT) x (Nat.cast (R := RangeT) 0) =
      Nat.cast (R := RangeT) 0 := by
  rw [alphaMulNorm_comm]
  exact alphaMulNorm_zero_left (RangeT := RangeT) x

/-- `Alpha.mulNorm max y = y`. -/
lemma alphaMulNorm_full_left {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (y : RangeT) :
    Alpha.mulNorm (RangeT := RangeT)
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) y = y := by
  have htoNatMax : ChannelFormat.toNat
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) =
      ChannelFormat.maxValue (RangeT := RangeT) := by
    exact LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT)
      (ChannelFormat.maxValue (RangeT := RangeT)) (Nat.le_refl _)
  have hmaxPos : 0 < ChannelFormat.maxValue (RangeT := RangeT) :=
    LawfulChannelFormat.maxValue_pos (RangeT := RangeT)
  have hdiv :
      Alpha.divRound
        ((ChannelFormat.maxValue (RangeT := RangeT)) * ChannelFormat.toNat y)
        (ChannelFormat.maxValue (RangeT := RangeT)) =
      ChannelFormat.toNat y := by
    simpa [Nat.mul_comm] using
      (alphaDivRound_mul_right (ChannelFormat.toNat y)
        (ChannelFormat.maxValue (RangeT := RangeT)) hmaxPos)
  unfold Alpha.mulNorm
  rw [htoNatMax]
  simpa [hdiv] using (alphaClamp_toNat_self (RangeT := RangeT) y)

/-- `Alpha.mulNorm x max = x`. -/
lemma alphaMulNorm_full_right {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (x : RangeT) :
    Alpha.mulNorm (RangeT := RangeT) x
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) = x := by
  rw [alphaMulNorm_comm]
  exact alphaMulNorm_full_left (RangeT := RangeT) x

/-- `Alpha.mulNorm 0 0 = 0`. -/
lemma alphaMulNorm_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] :
    Alpha.mulNorm (RangeT := RangeT) (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) =
      Nat.cast (R := RangeT) 0 := by
  exact alphaMulNorm_zero_left (RangeT := RangeT) (Nat.cast (R := RangeT) 0)

/-- `Alpha.mulNorm max max = max`. -/
lemma alphaMulNorm_full_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] :
    Alpha.mulNorm (RangeT := RangeT)
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)))
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  exact alphaMulNorm_full_left (RangeT := RangeT)
    (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)))

/-- Characterizes `toNat (Alpha.over dst src)` as a clamped over-alpha formula. -/
lemma alphaOver_toNat_eq_min {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dstA srcA : RangeT) :
    ChannelFormat.toNat (Alpha.over (RangeT := RangeT) dstA srcA) =
      Nat.min (ChannelFormat.maxValue (RangeT := RangeT))
        (ChannelFormat.toNat srcA +
          Alpha.divRound
            (ChannelFormat.toNat dstA *
              ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat srcA))
            (ChannelFormat.maxValue (RangeT := RangeT))) := by
  unfold Alpha.over
  exact alphaClamp_toNat_eq_min (RangeT := RangeT) _

/-- The `Nat` value of `Alpha.over dst src` is bounded by `maxValue`. -/
lemma alphaOver_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dstA srcA : RangeT) :
    ChannelFormat.toNat (Alpha.over (RangeT := RangeT) dstA srcA) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  rw [alphaOver_toNat_eq_min (RangeT := RangeT) dstA srcA]
  exact Nat.min_le_left _ _

/-- The blended channel value is always bounded by `maxValue` in `Nat` form. -/
lemma blendChannelOver_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dstC srcC dstA srcA : RangeT) :
    ChannelFormat.toNat (Alpha.blendChannelOver (RangeT := RangeT) dstC srcC dstA srcA) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  unfold Alpha.blendChannelOver
  dsimp
  split
  · simpa using (alphaClamp_toNat_le_max (RangeT := RangeT) 0)
  · simpa using
      (alphaClamp_toNat_le_max (RangeT := RangeT)
        (Alpha.divRound
          ((ChannelFormat.toNat srcC * ChannelFormat.toNat srcA +
              Alpha.divRound
                (ChannelFormat.toNat dstC * ChannelFormat.toNat dstA *
                  (ChannelFormat.maxValue (RangeT := RangeT) - ChannelFormat.toNat srcA))
                (ChannelFormat.maxValue (RangeT := RangeT))) *
            ChannelFormat.maxValue (RangeT := RangeT))
          (ChannelFormat.toNat srcA +
            Alpha.divRound
              (ChannelFormat.toNat dstA *
                (ChannelFormat.maxValue (RangeT := RangeT) - ChannelFormat.toNat srcA))
              (ChannelFormat.maxValue (RangeT := RangeT))))
      )

/-- With both alphas `0`, `Alpha.blendChannelOver` returns channel `0`. -/
lemma blendChannelOver_alpha_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dstC srcC : RangeT) :
    Alpha.blendChannelOver (RangeT := RangeT) dstC srcC
      (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) =
      Nat.cast (R := RangeT) 0 := by
  have htoNat0 : ChannelFormat.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  have hdiv0 :
      Alpha.divRound 0 (ChannelFormat.maxValue (RangeT := RangeT)) = 0 := by
    simpa using (alphaDivRound_zero_left (ChannelFormat.maxValue (RangeT := RangeT)))
  unfold Alpha.blendChannelOver
  unfold Alpha.clamp
  simp [htoNat0, hdiv0]

/-- With both input channel values `0`, `Alpha.blendChannelOver` returns `0`. -/
lemma blendChannelOver_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dstA srcA : RangeT) :
    Alpha.blendChannelOver (RangeT := RangeT)
      (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) dstA srcA =
      Nat.cast (R := RangeT) 0 := by
  have htoNat0 : ChannelFormat.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  unfold Alpha.blendChannelOver
  unfold Alpha.clamp
  simp [htoNat0, alphaDivRound_zero_left]

/-- `RGBA.over` computes alpha as `Alpha.over dst.a src.a`. -/
lemma rgbaOver_alpha {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.over (RangeT := RangeT) dst src).a = Alpha.over (RangeT := RangeT) dst.a src.a := by
  rfl

/-- `RGBA.multiplyOver` computes alpha as `Alpha.over dst.a src.a`. -/
lemma rgbaMultiplyOver_alpha {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).a =
      Alpha.over (RangeT := RangeT) dst.a src.a := by
  unfold RGBA.multiplyOver RGBA.over
  rfl

/-- For `RGBA.over`, source alpha is `0`, so output alpha is destination alpha. -/
lemma rgbaOver_alpha_src_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).a = dst.a := by
  rw [rgbaOver_alpha, hsrc]
  exact alphaOver_src_zero (RangeT := RangeT) dst.a

/-- For `RGBA.over`, destination alpha is `0`, so output alpha is source alpha. -/
lemma rgbaOver_alpha_dst_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).a = src.a := by
  rw [rgbaOver_alpha, hdst]
  exact alphaOver_dst_zero (RangeT := RangeT) src.a

/-- For `RGBA.over`, source alpha is maximal, so output alpha is maximal. -/
lemma rgbaOver_alpha_src_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (RGBA.over (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  rw [rgbaOver_alpha, hsrc]
  exact alphaOver_src_full (RangeT := RangeT) dst.a

/-- `toNat` of `RGBA.over` alpha is bounded by `maxValue`. -/
lemma rgbaOver_alpha_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).a) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_alpha] using
    (alphaOver_toNat_le_max (RangeT := RangeT) dst.a src.a)

/-- Characterizes `toNat` of `RGBA.over` alpha with the clamped over-alpha formula. -/
lemma rgbaOver_alpha_toNat_eq_min {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).a) =
      Nat.min (ChannelFormat.maxValue (RangeT := RangeT))
        (ChannelFormat.toNat src.a +
          Alpha.divRound
            (ChannelFormat.toNat dst.a *
              ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat src.a))
            (ChannelFormat.maxValue (RangeT := RangeT))) := by
  simpa [rgbaOver_alpha] using
    (alphaOver_toNat_eq_min (RangeT := RangeT) dst.a src.a)

/-- For `RGBA.multiplyOver`, source alpha is `0`, so output alpha is destination alpha. -/
lemma rgbaMultiplyOver_alpha_src_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).a = dst.a := by
  rw [rgbaMultiplyOver_alpha, hsrc]
  exact alphaOver_src_zero (RangeT := RangeT) dst.a

/-- For `RGBA.multiplyOver`, destination alpha is `0`, so output alpha is source alpha. -/
lemma rgbaMultiplyOver_alpha_dst_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).a = src.a := by
  rw [rgbaMultiplyOver_alpha, hdst]
  exact alphaOver_dst_zero (RangeT := RangeT) src.a

/-- For `RGBA.multiplyOver`, source alpha is maximal, so output alpha is maximal. -/
lemma rgbaMultiplyOver_alpha_src_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  rw [rgbaMultiplyOver_alpha, hsrc]
  exact alphaOver_src_full (RangeT := RangeT) dst.a

/-- `toNat` of `RGBA.multiplyOver` alpha is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_alpha_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).a) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_alpha] using
    (alphaOver_toNat_le_max (RangeT := RangeT) dst.a src.a)

/-- Characterizes `toNat` of `RGBA.multiplyOver` alpha with the clamped over-alpha formula. -/
lemma rgbaMultiplyOver_alpha_toNat_eq_min {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).a) =
      Nat.min (ChannelFormat.maxValue (RangeT := RangeT))
        (ChannelFormat.toNat src.a +
          Alpha.divRound
            (ChannelFormat.toNat dst.a *
              ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat src.a))
            (ChannelFormat.maxValue (RangeT := RangeT))) := by
  simpa [rgbaMultiplyOver_alpha] using
    (alphaOver_toNat_eq_min (RangeT := RangeT) dst.a src.a)

/-- `Alpha.over max src = max`. -/
lemma alphaOver_dst_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (srcA : RangeT) :
    Alpha.over (RangeT := RangeT)
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) srcA =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  have hdstMax : ChannelFormat.toNat
      (Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) =
      ChannelFormat.maxValue (RangeT := RangeT) := by
    exact LawfulChannelFormat.toNat_natCast_of_le_max (RangeT := RangeT)
      (ChannelFormat.maxValue (RangeT := RangeT)) (Nat.le_refl _)
  have hmaxPos : 0 < ChannelFormat.maxValue (RangeT := RangeT) :=
    LawfulChannelFormat.maxValue_pos (RangeT := RangeT)
  have hdiv :
      Alpha.divRound
        ((ChannelFormat.maxValue (RangeT := RangeT)) *
          ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat srcA))
        (ChannelFormat.maxValue (RangeT := RangeT)) =
      (ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat srcA := by
    simpa [Nat.mul_comm] using
      (alphaDivRound_mul_right
        ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat srcA)
        (ChannelFormat.maxValue (RangeT := RangeT)) hmaxPos)
  have hle : ChannelFormat.toNat srcA ≤ ChannelFormat.maxValue (RangeT := RangeT) :=
    LawfulChannelFormat.toNat_le_max (RangeT := RangeT) srcA
  have hs : ChannelFormat.toNat srcA +
      ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat srcA) =
      ChannelFormat.maxValue (RangeT := RangeT) := by
    exact Nat.add_sub_of_le hle
  have hcast : Alpha.clamp (RangeT := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
    unfold Alpha.clamp
    simp
  simpa [Alpha.over, hdstMax, hdiv, hs] using hcast

/-- `Alpha.over 0 0 = 0`. -/
lemma alphaOver_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] :
    Alpha.over (RangeT := RangeT) (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) =
      (Nat.cast (R := RangeT) 0) := by
  have h := alphaOver_dst_zero (RangeT := RangeT) (srcA := (Nat.cast (R := RangeT) 0))
  simpa using h

/-- For `RGBA.over`, destination alpha is maximal, so output alpha is maximal. -/
lemma rgbaOver_alpha_dst_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (RGBA.over (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  rw [rgbaOver_alpha, hdst]
  exact alphaOver_dst_full (RangeT := RangeT) src.a

/-- For `RGBA.multiplyOver`, destination alpha is maximal, so output alpha is maximal. -/
lemma rgbaMultiplyOver_alpha_dst_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  rw [rgbaMultiplyOver_alpha, hdst]
  exact alphaOver_dst_full (RangeT := RangeT) src.a

/-- For `RGBA.over`, both input alphas are `0`, so output alpha is `0`. -/
lemma rgbaOver_alpha_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).a = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_alpha, hdst, hsrc]
  exact alphaOver_zero_zero (RangeT := RangeT)

/-- For `RGBA.multiplyOver`, both input alphas are `0`, so output alpha is `0`. -/
lemma rgbaMultiplyOver_alpha_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).a = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_alpha, hdst, hsrc]
  exact alphaOver_zero_zero (RangeT := RangeT)

/-- Projects the red channel of `RGBA.over` to the corresponding `Alpha.blendChannelOver` expression. -/
lemma rgbaOver_r {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.over (RangeT := RangeT) dst src).r =
      Alpha.blendChannelOver (RangeT := RangeT) dst.r src.r dst.a src.a := by
  rfl

/-- Projects the green channel of `RGBA.over` to the corresponding `Alpha.blendChannelOver` expression. -/
lemma rgbaOver_g {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.over (RangeT := RangeT) dst src).g =
      Alpha.blendChannelOver (RangeT := RangeT) dst.g src.g dst.a src.a := by
  rfl

/-- Projects the blue channel of `RGBA.over` to the corresponding `Alpha.blendChannelOver` expression. -/
lemma rgbaOver_b {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.over (RangeT := RangeT) dst src).b =
      Alpha.blendChannelOver (RangeT := RangeT) dst.b src.b dst.a src.a := by
  rfl

/-- `toNat` of the red channel of `RGBA.over` is bounded by `maxValue`. -/
lemma rgbaOver_toNat_r_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).r) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_r] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT) dst.r src.r dst.a src.a)

/-- `toNat` of the green channel of `RGBA.over` is bounded by `maxValue`. -/
lemma rgbaOver_toNat_g_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).g) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_g] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT) dst.g src.g dst.a src.a)

/-- `toNat` of the blue channel of `RGBA.over` is bounded by `maxValue`. -/
lemma rgbaOver_toNat_b_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).b) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_b] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT) dst.b src.b dst.a src.a)

/-- All channel values of `RGBA.over` are bounded by `maxValue` after `toNat`. -/
lemma rgbaOver_channels_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).r) ≤
        ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).g) ≤
        ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).b) ≤
        ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((RGBA.over (RangeT := RangeT) dst src).a) ≤
        ChannelFormat.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact rgbaOver_toNat_r_le_max (RangeT := RangeT) dst src
  · exact rgbaOver_toNat_g_le_max (RangeT := RangeT) dst src
  · exact rgbaOver_toNat_b_le_max (RangeT := RangeT) dst src
  · exact rgbaOver_alpha_toNat_le_max (RangeT := RangeT) dst src

/-- For `RGBA.over`, if both input alphas are `0`, the red channel is `0`. -/
lemma rgbaOver_r_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_r]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT) dst.r src.r)

/-- For `RGBA.over`, if both input alphas are `0`, the green channel is `0`. -/
lemma rgbaOver_g_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_g]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT) dst.g src.g)

/-- For `RGBA.over`, if both input alphas are `0`, the blue channel is `0`. -/
lemma rgbaOver_b_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_b]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT) dst.b src.b)

/-- For `RGBA.over`, if both input red channels are `0`, the output red channel is `0`. -/
lemma rgbaOver_r_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_r, hdst, hsrc]
  exact blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a

/-- For `RGBA.over`, if both input green channels are `0`, the output green channel is `0`. -/
lemma rgbaOver_g_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_g, hdst, hsrc]
  exact blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a

/-- For `RGBA.over`, if both input blue channels are `0`, the output blue channel is `0`. -/
lemma rgbaOver_b_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_b, hdst, hsrc]
  exact blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a

/-- For `RGBA.over`, if both input RGB channels are all `0`, output RGB channels are all `0`. -/
lemma rgbaOver_rgb_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    (RGBA.over (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 ∧
    (RGBA.over (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 ∧
    (RGBA.over (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact rgbaOver_r_channel_zero_zero (RangeT := RangeT) dst src hdstR hsrcR
  · exact rgbaOver_g_channel_zero_zero (RangeT := RangeT) dst src hdstG hsrcG
  · exact rgbaOver_b_channel_zero_zero (RangeT := RangeT) dst src hdstB hsrcB

/-- Projects the red channel of `RGBA.multiplyOver` to the corresponding `Alpha.blendChannelOver` expression. -/
lemma rgbaMultiplyOver_r {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).r =
      Alpha.blendChannelOver (RangeT := RangeT)
        dst.r (Alpha.mulNorm (RangeT := RangeT) dst.r src.r) dst.a src.a := by
  simp [RGBA.multiplyOver, RGBA.over]

/-- Projects the green channel of `RGBA.multiplyOver` to the corresponding `Alpha.blendChannelOver` expression. -/
lemma rgbaMultiplyOver_g {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).g =
      Alpha.blendChannelOver (RangeT := RangeT)
        dst.g (Alpha.mulNorm (RangeT := RangeT) dst.g src.g) dst.a src.a := by
  simp [RGBA.multiplyOver, RGBA.over]

/-- Projects the blue channel of `RGBA.multiplyOver` to the corresponding `Alpha.blendChannelOver` expression. -/
lemma rgbaMultiplyOver_b {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).b =
      Alpha.blendChannelOver (RangeT := RangeT)
        dst.b (Alpha.mulNorm (RangeT := RangeT) dst.b src.b) dst.a src.a := by
  simp [RGBA.multiplyOver, RGBA.over]

/-- `toNat` of the red channel of `RGBA.multiplyOver` is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_toNat_r_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).r) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_r] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT)
      dst.r (Alpha.mulNorm (RangeT := RangeT) dst.r src.r) dst.a src.a)

/-- `toNat` of the green channel of `RGBA.multiplyOver` is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_toNat_g_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).g) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_g] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT)
      dst.g (Alpha.mulNorm (RangeT := RangeT) dst.g src.g) dst.a src.a)

/-- `toNat` of the blue channel of `RGBA.multiplyOver` is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_toNat_b_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).b) ≤
      ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_b] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT)
      dst.b (Alpha.mulNorm (RangeT := RangeT) dst.b src.b) dst.a src.a)

/-- All channel values of `RGBA.multiplyOver` are bounded by `maxValue` after `toNat`. -/
lemma rgbaMultiplyOver_channels_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).r) ≤
        ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).g) ≤
        ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).b) ≤
        ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((RGBA.multiplyOver (RangeT := RangeT) dst src).a) ≤
        ChannelFormat.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact rgbaMultiplyOver_toNat_r_le_max (RangeT := RangeT) dst src
  · exact rgbaMultiplyOver_toNat_g_le_max (RangeT := RangeT) dst src
  · exact rgbaMultiplyOver_toNat_b_le_max (RangeT := RangeT) dst src
  · exact rgbaMultiplyOver_alpha_toNat_le_max (RangeT := RangeT) dst src

/-- For `RGBA.multiplyOver`, if both input alphas are `0`, the red channel is `0`. -/
lemma rgbaMultiplyOver_r_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_r]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT)
      dst.r (Alpha.mulNorm (RangeT := RangeT) dst.r src.r))

/-- For `RGBA.multiplyOver`, if both input alphas are `0`, the green channel is `0`. -/
lemma rgbaMultiplyOver_g_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_g]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT)
      dst.g (Alpha.mulNorm (RangeT := RangeT) dst.g src.g))

/-- For `RGBA.multiplyOver`, if both input alphas are `0`, the blue channel is `0`. -/
lemma rgbaMultiplyOver_b_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_b]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT)
      dst.b (Alpha.mulNorm (RangeT := RangeT) dst.b src.b))

/-- For `RGBA.multiplyOver`, if both input red channels are `0`, the output red channel is `0`. -/
lemma rgbaMultiplyOver_r_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_r, hdst, hsrc]
  simpa [alphaMulNorm_zero_zero (RangeT := RangeT)] using
    (blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a)

/-- For `RGBA.multiplyOver`, if both input green channels are `0`, the output green channel is `0`. -/
lemma rgbaMultiplyOver_g_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_g, hdst, hsrc]
  simpa [alphaMulNorm_zero_zero (RangeT := RangeT)] using
    (blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a)

/-- For `RGBA.multiplyOver`, if both input blue channels are `0`, the output blue channel is `0`. -/
lemma rgbaMultiplyOver_b_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_b, hdst, hsrc]
  simpa [alphaMulNorm_zero_zero (RangeT := RangeT)] using
    (blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a)

/-- For `RGBA.multiplyOver`, if both input RGB channels are all `0`, output RGB channels are all `0`. -/
lemma rgbaMultiplyOver_rgb_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    (RGBA.multiplyOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 ∧
    (RGBA.multiplyOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 ∧
    (RGBA.multiplyOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact rgbaMultiplyOver_r_channel_zero_zero (RangeT := RangeT) dst src hdstR hsrcR
  · exact rgbaMultiplyOver_g_channel_zero_zero (RangeT := RangeT) dst src hdstG hsrcG
  · exact rgbaMultiplyOver_b_channel_zero_zero (RangeT := RangeT) dst src hdstB hsrcB

/-- For `RGBA.over`, if both input alphas are `0`, output is fully transparent black. -/
lemma rgbaOver_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    RGBA.over (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : RGBA RangeT) := by
  cases dst with
  | mk dr dg db da =>
    cases src with
    | mk sr sg sb sa =>
      simp at hdst hsrc
      subst da
      subst sa
      unfold RGBA.over
      simp [blendChannelOver_alpha_zero_zero, alphaOver_zero_zero]

/-- For `RGBA.multiplyOver`, if both input alphas are `0`, output is fully transparent black. -/
lemma rgbaMultiplyOver_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    RGBA.multiplyOver (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : RGBA RangeT) := by
  cases dst with
  | mk dr dg db da =>
    cases src with
    | mk sr sg sb sa =>
      simp at hdst hsrc
      subst da
      subst sa
      unfold RGBA.multiplyOver RGBA.over
      simp [blendChannelOver_alpha_zero_zero, alphaOver_zero_zero]

/-- For `RGBA.over`, if both input RGB channels are black, output RGB stays black and alpha is `Alpha.over dst.a src.a`. -/
lemma rgbaOver_black_channels {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    RGBA.over (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Alpha.over (RangeT := RangeT) dst.a src.a } : RGBA RangeT) := by
  cases dst with
  | mk dr dg db da =>
    cases src with
    | mk sr sg sb sa =>
      simp at hdstR hsrcR hdstG hsrcG hdstB hsrcB
      subst dr
      subst sr
      subst dg
      subst sg
      subst db
      subst sb
      unfold RGBA.over
      simp [blendChannelOver_channel_zero_zero]

/-- For `RGBA.multiplyOver`, if both input RGB channels are black, output RGB stays black and alpha is `Alpha.over dst.a src.a`. -/
lemma rgbaMultiplyOver_black_channels {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    RGBA.multiplyOver (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Alpha.over (RangeT := RangeT) dst.a src.a } : RGBA RangeT) := by
  cases dst with
  | mk dr dg db da =>
    cases src with
    | mk sr sg sb sa =>
      simp at hdstR hsrcR hdstG hsrcG hdstB hsrcB
      subst dr
      subst sr
      subst dg
      subst sg
      subst db
      subst sb
      unfold RGBA.multiplyOver RGBA.over
      simp [alphaMulNorm_zero_zero, blendChannelOver_channel_zero_zero]

/-- Bridges `dst + src` to `RGBA.over`. -/
lemma pixelRGBA_add_eq_rgbaOver {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    dst + src = RGBA.over (RangeT := RangeT) dst src := rfl

/-- Bridges `dst * src` to `RGBA.multiplyOver`. -/
lemma pixelRGBA_mul_eq_rgbaMultiplyOver {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    dst * src = RGBA.multiplyOver (RangeT := RangeT) dst src := rfl

/-- Alpha channel projection for `dst + src`. -/
lemma pixelRGBA_add_alpha {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst + src).a = Alpha.over (RangeT := RangeT) dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_alpha (RangeT := RangeT) dst src)

/-- Alpha channel projection for `dst * src`. -/
lemma pixelRGBA_mul_alpha {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst * src).a = Alpha.over (RangeT := RangeT) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_alpha (RangeT := RangeT) dst src)

/-- `dst + src` channel projection for the red channel. -/
lemma pixelRGBA_add_r {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst + src).r = Alpha.blendChannelOver (RangeT := RangeT) dst.r src.r dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_r (RangeT := RangeT) dst src)

/-- `dst + src` channel projection for the green channel. -/
lemma pixelRGBA_add_g {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst + src).g = Alpha.blendChannelOver (RangeT := RangeT) dst.g src.g dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_g (RangeT := RangeT) dst src)

/-- `dst + src` channel projection for the blue channel. -/
lemma pixelRGBA_add_b {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst + src).b = Alpha.blendChannelOver (RangeT := RangeT) dst.b src.b dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_b (RangeT := RangeT) dst src)

/-- `dst * src` channel projection for the red channel. -/
lemma pixelRGBA_mul_r {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst * src).r =
      Alpha.blendChannelOver (RangeT := RangeT)
        dst.r (Alpha.mulNorm (RangeT := RangeT) dst.r src.r) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_r (RangeT := RangeT) dst src)

/-- `dst * src` channel projection for the green channel. -/
lemma pixelRGBA_mul_g {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst * src).g =
      Alpha.blendChannelOver (RangeT := RangeT)
        dst.g (Alpha.mulNorm (RangeT := RangeT) dst.g src.g) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_g (RangeT := RangeT) dst src)

/-- `dst * src` channel projection for the blue channel. -/
lemma pixelRGBA_mul_b {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) :
    (dst * src).b =
      Alpha.blendChannelOver (RangeT := RangeT)
        dst.b (Alpha.mulNorm (RangeT := RangeT) dst.b src.b) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_b (RangeT := RangeT) dst src)

/-- `toNat` of the red channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_toNat_r_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst + src).r) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_toNat_r_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the green channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_toNat_g_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst + src).g) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_toNat_g_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the blue channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_toNat_b_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst + src).b) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_toNat_b_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the red channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_toNat_r_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst * src).r) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_toNat_r_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the green channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_toNat_g_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst * src).g) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_toNat_g_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the blue channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_toNat_b_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst * src).b) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_toNat_b_le_max (RangeT := RangeT) dst src)

/-- All channel values of `dst + src` are bounded by `maxValue` after `toNat`. -/
lemma pixelRGBA_add_channels_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst + src).r) ≤ ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((dst + src).g) ≤ ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((dst + src).b) ≤ ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((dst + src).a) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact pixelRGBA_add_toNat_r_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_add_toNat_g_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_add_toNat_b_le_max (RangeT := RangeT) dst src
  · simpa [pixelRGBA_add_eq_rgbaOver] using
      (rgbaOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- All channel values of `dst * src` are bounded by `maxValue` after `toNat`. -/
lemma pixelRGBA_mul_channels_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst * src).r) ≤ ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((dst * src).g) ≤ ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((dst * src).b) ≤ ChannelFormat.maxValue (RangeT := RangeT) ∧
    ChannelFormat.toNat ((dst * src).a) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact pixelRGBA_mul_toNat_r_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_mul_toNat_g_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_mul_toNat_b_le_max (RangeT := RangeT) dst src
  · simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
      (rgbaMultiplyOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- If both input alphas are `0`, the red channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_r_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_r_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the green channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_g_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_g_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the blue channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_b_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_b_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the red channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_r_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_r_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the green channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_g_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_g_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the blue channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_b_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_b_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input red channels are `0`, the output red channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_r_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (dst + src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_r_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input green channels are `0`, the output green channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_g_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (dst + src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_g_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input blue channels are `0`, the output blue channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_b_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (dst + src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_b_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input red channels are `0`, the output red channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_r_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (dst * src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_r_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input green channels are `0`, the output green channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_g_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (dst * src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_g_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input blue channels are `0`, the output blue channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_b_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (dst * src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_b_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input RGB channels are all `0`, the RGB channels of `dst + src` are all `0`. -/
lemma pixelRGBA_add_rgb_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    (dst + src).r = Nat.cast (R := RangeT) 0 ∧
    (dst + src).g = Nat.cast (R := RangeT) 0 ∧
    (dst + src).b = Nat.cast (R := RangeT) 0 := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact pixelRGBA_add_r_channel_zero_zero (RangeT := RangeT) dst src hdstR hsrcR
  · exact pixelRGBA_add_g_channel_zero_zero (RangeT := RangeT) dst src hdstG hsrcG
  · exact pixelRGBA_add_b_channel_zero_zero (RangeT := RangeT) dst src hdstB hsrcB

/-- If both input RGB channels are all `0`, the RGB channels of `dst * src` are all `0`. -/
lemma pixelRGBA_mul_rgb_channel_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    (dst * src).r = Nat.cast (R := RangeT) 0 ∧
    (dst * src).g = Nat.cast (R := RangeT) 0 ∧
    (dst * src).b = Nat.cast (R := RangeT) 0 := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact pixelRGBA_mul_r_channel_zero_zero (RangeT := RangeT) dst src hdstR hsrcR
  · exact pixelRGBA_mul_g_channel_zero_zero (RangeT := RangeT) dst src hdstG hsrcG
  · exact pixelRGBA_mul_b_channel_zero_zero (RangeT := RangeT) dst src hdstB hsrcB

/-- If both input alphas are `0`, `dst + src` yields fully transparent black. -/
lemma pixelRGBA_add_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    dst + src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : RGBA RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, `dst * src` yields fully transparent black. -/
lemma pixelRGBA_mul_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    dst * src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : RGBA RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input RGB channels are black, `dst + src` keeps RGB black and computes alpha with `Alpha.over`. -/
lemma pixelRGBA_add_black_channels {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    dst + src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Alpha.over (RangeT := RangeT) dst.a src.a } : RGBA RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_black_channels (RangeT := RangeT) dst src
      hdstR hsrcR hdstG hsrcG hdstB hsrcB)

/-- If both input RGB channels are black, `dst * src` keeps RGB black and computes alpha with `Alpha.over`. -/
lemma pixelRGBA_mul_black_channels {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    dst * src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Alpha.over (RangeT := RangeT) dst.a src.a } : RGBA RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_black_channels (RangeT := RangeT) dst src
      hdstR hsrcR hdstG hsrcG hdstB hsrcB)

/-- `toNat` of the alpha channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_alpha_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst + src).a) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the alpha channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_alpha_toNat_le_max {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst * src).a) ≤ ChannelFormat.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- Characterizes `toNat` of the alpha channel of `dst + src` with the clamped over-alpha formula. -/
lemma pixelRGBA_add_alpha_toNat_eq_min {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst + src).a) =
      Nat.min (ChannelFormat.maxValue (RangeT := RangeT))
        (ChannelFormat.toNat src.a +
          Alpha.divRound
            (ChannelFormat.toNat dst.a *
              ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat src.a))
            (ChannelFormat.maxValue (RangeT := RangeT))) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_toNat_eq_min (RangeT := RangeT) dst src)

/-- Characterizes `toNat` of the alpha channel of `dst * src` with the clamped over-alpha formula. -/
lemma pixelRGBA_mul_alpha_toNat_eq_min {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT) :
    ChannelFormat.toNat ((dst * src).a) =
      Nat.min (ChannelFormat.maxValue (RangeT := RangeT))
        (ChannelFormat.toNat src.a +
          Alpha.divRound
            (ChannelFormat.toNat dst.a *
              ((ChannelFormat.maxValue (RangeT := RangeT)) - ChannelFormat.toNat src.a))
            (ChannelFormat.maxValue (RangeT := RangeT))) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_toNat_eq_min (RangeT := RangeT) dst src)

/-- For `dst + src`, source alpha is `0`, so output alpha is destination alpha. -/
lemma pixelRGBA_add_alpha_src_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).a = dst.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_src_zero (RangeT := RangeT) dst src hsrc)

/-- For `dst + src`, destination alpha is `0`, so output alpha is source alpha. -/
lemma pixelRGBA_add_alpha_dst_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (dst + src).a = src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_dst_zero (RangeT := RangeT) dst src hdst)

/-- For `dst + src`, source alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_add_alpha_src_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (dst + src).a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_src_full (RangeT := RangeT) dst src hsrc)

/-- For `dst + src`, destination alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_add_alpha_dst_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (dst + src).a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_dst_full (RangeT := RangeT) dst src hdst)

/-- For `dst + src`, both input alphas are `0`, so output alpha is `0`. -/
lemma pixelRGBA_add_alpha_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).a = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- For `dst * src`, source alpha is `0`, so output alpha is destination alpha. -/
lemma pixelRGBA_mul_alpha_src_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).a = dst.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_src_zero (RangeT := RangeT) dst src hsrc)

/-- For `dst * src`, destination alpha is `0`, so output alpha is source alpha. -/
lemma pixelRGBA_mul_alpha_dst_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (dst * src).a = src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_dst_zero (RangeT := RangeT) dst src hdst)

/-- For `dst * src`, source alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_mul_alpha_src_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (dst * src).a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_src_full (RangeT := RangeT) dst src hsrc)

/-- For `dst * src`, destination alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_mul_alpha_dst_full {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT))) :
    (dst * src).a = Nat.cast (R := RangeT) (ChannelFormat.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_dst_full (RangeT := RangeT) dst src hdst)

/-- For `dst * src`, both input alphas are `0`, so output alpha is `0`. -/
lemma pixelRGBA_mul_alpha_zero_zero {RangeT : Type u} [ChannelFormat RangeT]
    [LawfulChannelFormat RangeT] (dst src : RGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).a = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_zero_zero (RangeT := RangeT) dst src hdst hsrc)

end Lemmas

end Bitmaps
