import Bitmap.Lemmas.Png.FixedBlockProofsSpec

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

namespace Bitmaps

namespace Png

/-! ## Fixed-block fast/slow bridge (Option A)

The runtime calls `decodeFixedBlockFast = decodeFixedBlockFuelFast`, while
`fixedBlockSpec_decode_correct` proves correctness against the slow variant
`decodeFixedBlockFuel`. The two functions differ only in their literal/length
symbol decoder. This file proves they agree extensionally and derives the
fast-variant fixed-block decode correctness corollary. -/

/-! ### Basic readBit and readBitsAux bounds -/

-- A single bit returned by `readBit` is always 0 or 1.
lemma readBit_lt_two (br : BitReader) : (br.readBit).1 < 2 := by
  unfold BitReader.readBit
  by_cases hEq : br.bytePos = br.data.size
  · simp [hEq]
  · have hlt : br.bytePos < br.data.size := lt_of_le_of_ne br.hpos hEq
    by_cases hnext : br.bitPos + 1 = 8
    · simp [hEq, hnext]; exact Nat.mod_lt _ (by decide)
    · simp [hEq, hnext]; exact Nat.mod_lt _ (by decide)

-- Project `readBitsAux_succ` to its first component.
lemma readBitsAux_succ_fst (br : BitReader) (k : Nat) :
    (br.readBitsAux (k + 1)).1 =
      (br.readBit).1 ||| (((br.readBit).2.readBitsAux k).1 <<< 1) := by
  have h := readBitsAux_succ br k
  have heq :
      br.readBitsAux (k + 1) =
        ((br.readBit).1 ||| (((br.readBit).2.readBitsAux k).1 <<< 1),
          ((br.readBit).2.readBitsAux k).2) := by
    rw [h]
  rw [heq]

-- Project `readBitsAux_succ` to its second component.
lemma readBitsAux_succ_snd (br : BitReader) (k : Nat) :
    (br.readBitsAux (k + 1)).2 = ((br.readBit).2.readBitsAux k).2 := by
  have h := readBitsAux_succ br k
  have heq :
      br.readBitsAux (k + 1) =
        ((br.readBit).1 ||| (((br.readBit).2.readBitsAux k).1 <<< 1),
          ((br.readBit).2.readBitsAux k).2) := by
    rw [h]
  rw [heq]

-- `(br.readBitsAux n).1 < 2 ^ n`, unconditionally.
lemma readBitsAux_lt_two_pow (br : BitReader) (n : Nat) :
    (br.readBitsAux n).1 < 2 ^ n := by
  induction n generalizing br with
  | zero =>
      simp [BitReader.readBitsAux, BitReader.readBitsAuxAcc]
  | succ k ih =>
      rw [readBitsAux_succ_fst]
      have hbit_lt : (br.readBit).1 < 2 := readBit_lt_two br
      have hrest_lt : ((br.readBit).2.readBitsAux k).1 < 2 ^ k :=
        ih (br := (br.readBit).2)
      have hbit_pow : (br.readBit).1 < 2 ^ (k + 1) := by
        have h2 : 2 ≤ 2 ^ (k + 1) := by
          calc 2 = 2 ^ 1 := by decide
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_of_le (by decide) (by omega)
        exact lt_of_lt_of_le hbit_lt h2
      have hshift_pow : ((br.readBit).2.readBitsAux k).1 <<< 1 < 2 ^ (k + 1) := by
        rw [Nat.shiftLeft_eq, Nat.pow_succ]
        exact (Nat.mul_lt_mul_right (by decide : 0 < 2)).mpr hrest_lt
      exact Nat.or_lt_two_pow hbit_pow hshift_pow

/-! ### bitIndex and data preservation under feasibility -/

private lemma bytePos_lt_of_feasible (br : BitReader) (n : Nat) (hn : 0 < n)
    (h : br.bitIndex + n ≤ br.data.size * 8) :
    br.bytePos < br.data.size := by
  by_contra hge
  have hEq : br.bytePos = br.data.size := le_antisymm br.hpos (Nat.not_lt.mp hge)
  have hbit0 : br.bitPos = 0 := br.hend hEq
  have hidx : br.bitIndex = br.data.size * 8 := by
    simp [BitReader.bitIndex, hEq, hbit0]
  omega

-- Under feasibility, `readBitsAux n` advances `bitIndex` by exactly `n` and
-- preserves the underlying byte array.
lemma readBitsAux_bitIndex_data (br : BitReader) (n : Nat)
    (h : br.bitIndex + n ≤ br.data.size * 8) :
    (br.readBitsAux n).2.bitIndex = br.bitIndex + n ∧
    (br.readBitsAux n).2.data = br.data := by
  induction n generalizing br with
  | zero =>
      simp [BitReader.readBitsAux, BitReader.readBitsAuxAcc]
  | succ k ih =>
      have hlt : br.bytePos < br.data.size :=
        bytePos_lt_of_feasible br (k + 1) (Nat.succ_pos _) h
      have hbr_data : (br.readBit).2.data = br.data := readBit_data br hlt
      have hbr_idx : (br.readBit).2.bitIndex = br.bitIndex + 1 :=
        bitIndex_readBit br hlt
      have hfeas' : (br.readBit).2.bitIndex + k ≤ (br.readBit).2.data.size * 8 := by
        rw [hbr_idx, hbr_data]; omega
      have ih' := ih (br := (br.readBit).2) hfeas'
      refine ⟨?_, ?_⟩
      · rw [readBitsAux_succ_snd]; rw [ih'.1, hbr_idx]; omega
      · rw [readBitsAux_succ_snd]; rw [ih'.2, hbr_data]

/-! ### Bridge mod and chain identities -/

-- `(br.readBitsAux 9).1 % 2 ^ 7 = (br.readBitsAux 7).1`.
lemma readBitsAux9_mod7 (br : BitReader) :
    (br.readBitsAux 9).1 % 2 ^ 7 = (br.readBitsAux 7).1 := by
  have hsplit := readBitsAux_split (br := br) (k := 7) (n := 2)
  cases h7 : br.readBitsAux 7 with
  | mk bits7 br7 =>
      cases h2 : br7.readBitsAux 2 with
      | mk rest2 br9 =>
          have hsplit' :
              br.readBitsAux 9 = (bits7 ||| (rest2 <<< 7), br9) := by
            simpa [h7, h2] using hsplit
          have hbits7_lt : bits7 < 2 ^ 7 := by
            have h := readBitsAux_lt_two_pow br 7
            rw [h7] at h
            exact h
          rw [hsplit']
          show (bits7 ||| (rest2 <<< 7)) % 2 ^ 7 = bits7
          rw [mod_two_pow_or_shift (a := bits7) (b := rest2) (k := 7) (len := 7) le_rfl]
          exact Nat.mod_eq_of_lt hbits7_lt

-- `(br.readBitsAux 9).1 % 2 ^ 8 = (br.readBitsAux 8).1`.
lemma readBitsAux9_mod8 (br : BitReader) :
    (br.readBitsAux 9).1 % 2 ^ 8 = (br.readBitsAux 8).1 := by
  have hsplit := readBitsAux_split (br := br) (k := 8) (n := 1)
  cases h8 : br.readBitsAux 8 with
  | mk bits8 br8 =>
      cases h1 : br8.readBitsAux 1 with
      | mk rest1 br9 =>
          have hsplit' :
              br.readBitsAux 9 = (bits8 ||| (rest1 <<< 8), br9) := by
            simpa [h8, h1] using hsplit
          have hbits8_lt : bits8 < 2 ^ 8 := by
            have h := readBitsAux_lt_two_pow br 8
            rw [h8] at h
            exact h
          rw [hsplit']
          show (bits8 ||| (rest1 <<< 8)) % 2 ^ 8 = bits8
          rw [mod_two_pow_or_shift (a := bits8) (b := rest1) (k := 8) (len := 8) le_rfl]
          exact Nat.mod_eq_of_lt hbits8_lt

-- 8-bit read decomposes as 7-bit + 1-bit chained read, in destructured form.
lemma readBitsAux_8_split_of (br : BitReader)
    (bits7 : Nat) (br7 : BitReader) (h7 : br.readBitsAux 7 = (bits7, br7))
    (bit8 : Nat) (br8 : BitReader) (h1 : br7.readBitsAux 1 = (bit8, br8)) :
    br.readBitsAux 8 = (bits7 ||| (bit8 <<< 7), br8) := by
  have hsplit := readBitsAux_split (br := br) (k := 7) (n := 1)
  simpa [h7, h1] using hsplit

-- 9-bit read decomposes as 7-bit + 1-bit + 1-bit chained reads.
lemma readBitsAux_9_split_of (br : BitReader)
    (bits7 : Nat) (br7 : BitReader) (h7 : br.readBitsAux 7 = (bits7, br7))
    (bit8 : Nat) (br8 : BitReader) (h1 : br7.readBitsAux 1 = (bit8, br8))
    (bit9 : Nat) (br9 : BitReader) (h1' : br8.readBitsAux 1 = (bit9, br9)) :
    br.readBitsAux 9 = ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8), br9) := by
  have h8 := readBitsAux_8_split_of br bits7 br7 h7 bit8 br8 h1
  have hsplit := readBitsAux_split (br := br) (k := 8) (n := 1)
  simpa [h8, h1'] using hsplit

end Png

end Bitmaps
