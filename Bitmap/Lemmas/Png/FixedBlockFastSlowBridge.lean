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

/-! ### Per-row characterization lemmas for the fast variant

These mirror the existing `decodeFixedLiteralSym_row7/_row8/_row9` lemmas
for the slow path. Together with those, they form the case-by-case bridge
to the slow decoder.

The slow `decodeFixedLiteralSym` outputs `some (sym, br7)` when the first
7-bit read produces `bits7` and `row7[bits7]? = some (some sym)`. The
fast variant uses `(br.readBitsAux 9).1 % 2 ^ 7 = (br.readBitsAux 7).1`
(`readBitsAux9_mod7`) plus `readBitsFastU32_eq_readBitsAux` to reduce
its row7 outcome to the same `bits7` and produces the same `br7`. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSymFast9_row7 (br : BitReader)
    (sym bits9 bits7 : Nat) (br9 br7 : BitReader)
    (h9 : br.bitIndex + 9 ≤ br.data.size * 8)
    (hbits9 : br.readBitsFastU32 9 h9 = (bits9, br9))
    (hbits7_eq : bits9 % 2 ^ 7 = bits7)
    (hrow7 : fixedLitLenRow7[bits7]? = some (some sym))
    (h7 : br.bitIndex + 7 ≤ br.data.size * 8)
    (hbr7 : (br.readBitsFastU32 7 h7).2 = br7) :
    decodeFixedLiteralSymFast9 br = some (sym, br7) := by
  unfold decodeFixedLiteralSymFast9
  simp [h9, hbits9, hbits7_eq, hrow7, h7, hbr7]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSymFast9_row8 (br : BitReader)
    (sym bits9 bits7 bits8 : Nat) (br9 br8 : BitReader)
    (h9 : br.bitIndex + 9 ≤ br.data.size * 8)
    (hbits9 : br.readBitsFastU32 9 h9 = (bits9, br9))
    (hbits7_eq : bits9 % 2 ^ 7 = bits7)
    (hrow7 : fixedLitLenRow7[bits7]? = none ∨ fixedLitLenRow7[bits7]? = some none)
    (hbits8_eq : bits9 % 2 ^ 8 = bits8)
    (hrow8 : fixedLitLenRow8[bits8]? = some (some sym))
    (h8 : br.bitIndex + 8 ≤ br.data.size * 8)
    (hbr8 : (br.readBitsFastU32 8 h8).2 = br8) :
    decodeFixedLiteralSymFast9 br = some (sym, br8) := by
  unfold decodeFixedLiteralSymFast9
  rcases hrow7 with h7n | h7n <;>
    simp [h9, hbits9, hbits7_eq, h7n, hbits8_eq, hrow8, h8, hbr8]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSymFast9_row9 (br : BitReader)
    (sym bits9 bits7 bits8 : Nat) (br9 : BitReader)
    (h9 : br.bitIndex + 9 ≤ br.data.size * 8)
    (hbits9 : br.readBitsFastU32 9 h9 = (bits9, br9))
    (hbits7_eq : bits9 % 2 ^ 7 = bits7)
    (hrow7 : fixedLitLenRow7[bits7]? = none ∨ fixedLitLenRow7[bits7]? = some none)
    (hbits8_eq : bits9 % 2 ^ 8 = bits8)
    (hrow8 : fixedLitLenRow8[bits8]? = none ∨ fixedLitLenRow8[bits8]? = some none)
    (hrow9 : fixedLitLenRow9[bits9]? = some (some sym)) :
    decodeFixedLiteralSymFast9 br = some (sym, br9) := by
  unfold decodeFixedLiteralSymFast9
  rcases hrow7 with h7n | h7n <;> rcases hrow8 with h8n | h8n <;>
    simp [h9, hbits9, hbits7_eq, h7n, hbits8_eq, h8n, hrow9]

-- "None" characterization: if no row matches, both functions return `none`.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSymFast9_none (br : BitReader)
    (bits9 bits7 bits8 : Nat) (br9 : BitReader)
    (h9 : br.bitIndex + 9 ≤ br.data.size * 8)
    (hbits9 : br.readBitsFastU32 9 h9 = (bits9, br9))
    (hbits7_eq : bits9 % 2 ^ 7 = bits7)
    (hrow7 : fixedLitLenRow7[bits7]? = none ∨ fixedLitLenRow7[bits7]? = some none)
    (hbits8_eq : bits9 % 2 ^ 8 = bits8)
    (hrow8 : fixedLitLenRow8[bits8]? = none ∨ fixedLitLenRow8[bits8]? = some none)
    (hrow9 : fixedLitLenRow9[bits9]? = none ∨ fixedLitLenRow9[bits9]? = some none) :
    decodeFixedLiteralSymFast9 br = none := by
  unfold decodeFixedLiteralSymFast9
  rcases hrow7 with h7n | h7n <;> rcases hrow8 with h8n | h8n <;> rcases hrow9 with h9n | h9n <;>
    simp [h9, hbits9, hbits7_eq, hbits8_eq, h7n, h8n, h9n]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSym_none (br : BitReader)
    (bits7 bit8 bit9 : Nat) (br7 br8 br9 : BitReader)
    (h7 : br.bitIndex + 7 ≤ br.data.size * 8)
    (hbits7 : br.readBits 7 h7 = (bits7, br7))
    (hrow7 : fixedLitLenRow7[bits7]? = none ∨ fixedLitLenRow7[bits7]? = some none)
    (h1 : br7.bitIndex + 1 ≤ br7.data.size * 8)
    (hbits8 : br7.readBits 1 h1 = (bit8, br8))
    (hrow8 : fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? = none ∨
             fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? = some none)
    (h1' : br8.bitIndex + 1 ≤ br8.data.size * 8)
    (hbits9 : br8.readBits 1 h1' = (bit9, br9))
    (hrow9 : fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? = none ∨
             fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? = some none) :
    decodeFixedLiteralSym br = none := by
  unfold decodeFixedLiteralSym
  have hf7 : br.readBitsFast 7 h7 = (bits7, br7) := by
    simpa [readBitsFast_eq_readBits (br := br) (n := 7) (h := h7)] using hbits7
  have hf1 : br7.readBitsFast 1 h1 = (bit8, br8) := by
    simpa [readBitsFast_eq_readBits (br := br7) (n := 1) (h := h1)] using hbits8
  have hf1' : br8.readBitsFast 1 h1' = (bit9, br9) := by
    simpa [readBitsFast_eq_readBits (br := br8) (n := 1) (h := h1')] using hbits9
  rcases hrow7 with h7n | h7n <;> rcases hrow8 with h8n | h8n <;> rcases hrow9 with h9n | h9n <;>
    simp [h7, hf7, h7n, h1, hf1, h8n, h1', hf1', h9n]

-- Slow row8 with disjunctive row7 condition (row7 is `none` or `some none`).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSym_row8_dis (br : BitReader)
    (sym bits7 bit8 : Nat) (br7 br8 : BitReader)
    (h7 : br.bitIndex + 7 ≤ br.data.size * 8)
    (hbits7 : br.readBits 7 h7 = (bits7, br7))
    (hrow7 : fixedLitLenRow7[bits7]? = none ∨ fixedLitLenRow7[bits7]? = some none)
    (h1 : br7.bitIndex + 1 ≤ br7.data.size * 8)
    (hbits8 : br7.readBits 1 h1 = (bit8, br8))
    (hrow8 : fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? = some (some sym)) :
    decodeFixedLiteralSym br = some (sym, br8) := by
  unfold decodeFixedLiteralSym
  have hf7 : br.readBitsFast 7 h7 = (bits7, br7) := by
    simpa [readBitsFast_eq_readBits (br := br) (n := 7) (h := h7)] using hbits7
  have hf1 : br7.readBitsFast 1 h1 = (bit8, br8) := by
    simpa [readBitsFast_eq_readBits (br := br7) (n := 1) (h := h1)] using hbits8
  rcases hrow7 with h7n | h7n <;> simp [h7, hf7, h7n, h1, hf1, hrow8]

-- Slow row9 with disjunctive row7/row8 conditions.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSym_row9_dis (br : BitReader)
    (sym bits7 bit8 bit9 : Nat) (br7 br8 br9 : BitReader)
    (h7 : br.bitIndex + 7 ≤ br.data.size * 8)
    (hbits7 : br.readBits 7 h7 = (bits7, br7))
    (hrow7 : fixedLitLenRow7[bits7]? = none ∨ fixedLitLenRow7[bits7]? = some none)
    (h1 : br7.bitIndex + 1 ≤ br7.data.size * 8)
    (hbits8 : br7.readBits 1 h1 = (bit8, br8))
    (hrow8 : fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? = none ∨
             fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? = some none)
    (h1' : br8.bitIndex + 1 ≤ br8.data.size * 8)
    (hbits9 : br8.readBits 1 h1' = (bit9, br9))
    (hrow9 : fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? = some (some sym)) :
    decodeFixedLiteralSym br = some (sym, br9) := by
  unfold decodeFixedLiteralSym
  have hf7 : br.readBitsFast 7 h7 = (bits7, br7) := by
    simpa [readBitsFast_eq_readBits (br := br) (n := 7) (h := h7)] using hbits7
  have hf1 : br7.readBitsFast 1 h1 = (bit8, br8) := by
    simpa [readBitsFast_eq_readBits (br := br7) (n := 1) (h := h1)] using hbits8
  have hf1' : br8.readBitsFast 1 h1' = (bit9, br9) := by
    simpa [readBitsFast_eq_readBits (br := br8) (n := 1) (h := h1')] using hbits9
  rcases hrow7 with h7n | h7n <;> rcases hrow8 with h8n | h8n <;>
    simp [h7, hf7, h7n, h1, hf1, h8n, h1', hf1', hrow9]

/-! ### Per-symbol bridge -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma decodeFixedLiteralSymFast9_eq_decodeFixedLiteralSym (br : BitReader) :
    decodeFixedLiteralSymFast9 br = decodeFixedLiteralSym br := by
  by_cases h9 : br.bitIndex + 9 ≤ br.data.size * 8
  · -- 9 bits available. All sequential reads are feasible.
    have h7 : br.bitIndex + 7 ≤ br.data.size * 8 := by omega
    have h8 : br.bitIndex + 8 ≤ br.data.size * 8 := by omega
    have hidx7 := readBitsAux_bitIndex_data br 7 h7
    -- Destructure the sequential reads via readBitsAux.
    cases h7eq : br.readBitsAux 7 with
    | mk bits7 br7 =>
        have h7'idx : br7.bitIndex = br.bitIndex + 7 := by
          have h := hidx7.1; rw [h7eq] at h; exact h
        have h7'data : br7.data = br.data := by
          have h := hidx7.2; rw [h7eq] at h; exact h
        have h1on7 : br7.bitIndex + 1 ≤ br7.data.size * 8 := by
          rw [h7'idx, h7'data]; omega
        have hidx1on7 := readBitsAux_bitIndex_data br7 1 h1on7
        cases h1eq : br7.readBitsAux 1 with
        | mk bit8 br8 =>
            have hbr8idx : br8.bitIndex = br7.bitIndex + 1 := by
              have h := hidx1on7.1; rw [h1eq] at h; exact h
            have hbr8data : br8.data = br7.data := by
              have h := hidx1on7.2; rw [h1eq] at h; exact h
            have h1on8 : br8.bitIndex + 1 ≤ br8.data.size * 8 := by
              rw [hbr8idx, hbr8data, h7'idx, h7'data]; omega
            cases h1eq' : br8.readBitsAux 1 with
            | mk bit9 br9 =>
                -- Slow side: bits at each step.
                have hslow7 : br.readBits 7 h7 = (bits7, br7) := by
                  rw [readBits_eq_readBitsAux]; exact h7eq
                have hslow1 : br7.readBits 1 h1on7 = (bit8, br8) := by
                  rw [readBits_eq_readBitsAux]; exact h1eq
                have hslow1' : br8.readBits 1 h1on8 = (bit9, br9) := by
                  rw [readBits_eq_readBitsAux]; exact h1eq'
                -- Fast side: identify bits9, br9_fast via readBitsFastU32 = readBitsAux.
                have hfast9_aux : br.readBitsFastU32 9 h9 = br.readBitsAux 9 :=
                  readBitsFastU32_eq_readBitsAux (br := br) (n := 9) (h := h9)
                have hfast7_aux : br.readBitsFastU32 7 h7 = br.readBitsAux 7 :=
                  readBitsFastU32_eq_readBitsAux (br := br) (n := 7) (h := h7)
                have hfast8_aux : br.readBitsFastU32 8 h8 = br.readBitsAux 8 :=
                  readBitsFastU32_eq_readBitsAux (br := br) (n := 8) (h := h8)
                -- Decomp lemmas: identify br.readBitsAux 8 and 9.
                have h8decomp :
                    br.readBitsAux 8 = (bits7 ||| (bit8 <<< 7), br8) :=
                  readBitsAux_8_split_of br bits7 br7 h7eq bit8 br8 h1eq
                have h9decomp :
                    br.readBitsAux 9 =
                      ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8), br9) :=
                  readBitsAux_9_split_of br bits7 br7 h7eq bit8 br8 h1eq bit9 br9 h1eq'
                -- Fast side readBitsFastU32 9 = (bits9_fast, br9_fast) with concrete values.
                have hfast9 :
                    br.readBitsFastU32 9 h9 =
                      ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8), br9) := by
                  rw [hfast9_aux, h9decomp]
                have hfast7 :
                    (br.readBitsFastU32 7 h7).2 = br7 := by
                  rw [hfast7_aux, h7eq]
                have hfast8 :
                    (br.readBitsFastU32 8 h8).2 = br8 := by
                  rw [hfast8_aux, h8decomp]
                -- mod identities for the fast side.
                have hmod7 :
                    ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) % 2 ^ 7 = bits7 := by
                  have hm := readBitsAux9_mod7 br
                  rw [h9decomp, h7eq] at hm
                  simpa using hm
                have hmod8 :
                    ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) % 2 ^ 8 =
                      bits7 ||| (bit8 <<< 7) := by
                  have hm := readBitsAux9_mod8 br
                  rw [h9decomp, h8decomp] at hm
                  simpa using hm
                -- Case-analyse on row7/row8/row9 outcomes.
                cases hr7 : fixedLitLenRow7[bits7]? with
                | none =>
                    cases hr8 : fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? with
                    | none =>
                        cases hr9 : fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? with
                        | none =>
                            rw [decodeFixedLiteralSymFast9_none br
                                ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                (Or.inl hr7) hmod8 (Or.inl hr8) (Or.inl hr9)]
                            rw [decodeFixedLiteralSym_none br bits7 bit8 bit9 br7 br8 br9
                                h7 hslow7 (Or.inl hr7) h1on7 hslow1 (Or.inl hr8)
                                h1on8 hslow1' (Or.inl hr9)]
                        | some o9 =>
                            cases o9 with
                            | none =>
                                rw [decodeFixedLiteralSymFast9_none br
                                    ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                    (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                    (Or.inl hr7) hmod8 (Or.inl hr8) (Or.inr hr9)]
                                rw [decodeFixedLiteralSym_none br bits7 bit8 bit9 br7 br8 br9
                                    h7 hslow7 (Or.inl hr7) h1on7 hslow1 (Or.inl hr8)
                                    h1on8 hslow1' (Or.inr hr9)]
                            | some sym9 =>
                                rw [decodeFixedLiteralSymFast9_row9 br sym9
                                    ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                    (bits7 ||| (bit8 <<< 7)) br9
                                    h9 hfast9 hmod7 (Or.inl hr7) hmod8 (Or.inl hr8) hr9]
                                rw [decodeFixedLiteralSym_row9_dis br sym9 bits7 bit8 bit9
                                    br7 br8 br9 h7 hslow7 (Or.inl hr7) h1on7 hslow1
                                    (Or.inl hr8) h1on8 hslow1' hr9]
                    | some o8 =>
                        cases o8 with
                        | none =>
                            cases hr9 : fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? with
                            | none =>
                                rw [decodeFixedLiteralSymFast9_none br
                                    ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                    (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                    (Or.inl hr7) hmod8 (Or.inr hr8) (Or.inl hr9)]
                                rw [decodeFixedLiteralSym_none br bits7 bit8 bit9 br7 br8 br9
                                    h7 hslow7 (Or.inl hr7) h1on7 hslow1 (Or.inr hr8)
                                    h1on8 hslow1' (Or.inl hr9)]
                            | some o9 =>
                                cases o9 with
                                | none =>
                                    rw [decodeFixedLiteralSymFast9_none br
                                        ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                        (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                        (Or.inl hr7) hmod8 (Or.inr hr8) (Or.inr hr9)]
                                    rw [decodeFixedLiteralSym_none br bits7 bit8 bit9 br7 br8 br9
                                        h7 hslow7 (Or.inl hr7) h1on7 hslow1 (Or.inr hr8)
                                        h1on8 hslow1' (Or.inr hr9)]
                                | some sym9 =>
                                    rw [decodeFixedLiteralSymFast9_row9 br sym9
                                        ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                        (bits7 ||| (bit8 <<< 7)) br9
                                        h9 hfast9 hmod7 (Or.inl hr7) hmod8 (Or.inr hr8) hr9]
                                    rw [decodeFixedLiteralSym_row9_dis br sym9 bits7 bit8 bit9
                                        br7 br8 br9 h7 hslow7 (Or.inl hr7) h1on7 hslow1
                                        (Or.inr hr8) h1on8 hslow1' hr9]
                        | some sym8 =>
                            rw [decodeFixedLiteralSymFast9_row8 br sym8
                                ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                (bits7 ||| (bit8 <<< 7)) br9 br8
                                h9 hfast9 hmod7 (Or.inl hr7) hmod8 hr8 h8 hfast8]
                            rw [decodeFixedLiteralSym_row8_dis br sym8 bits7 bit8 br7 br8
                                h7 hslow7 (Or.inl hr7) h1on7 hslow1 hr8]
                | some o7 =>
                    cases o7 with
                    | none =>
                        -- Same sub-tree as the `none` outer case; duplicated due to the
                        -- nested `some none` shape that the row7 lookup may produce.
                        cases hr8 : fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? with
                        | none =>
                            cases hr9 : fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? with
                            | none =>
                                rw [decodeFixedLiteralSymFast9_none br
                                    ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                    (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                    (Or.inr hr7) hmod8 (Or.inl hr8) (Or.inl hr9)]
                                rw [decodeFixedLiteralSym_none br bits7 bit8 bit9 br7 br8 br9
                                    h7 hslow7 (Or.inr hr7) h1on7 hslow1 (Or.inl hr8)
                                    h1on8 hslow1' (Or.inl hr9)]
                            | some o9 =>
                                cases o9 with
                                | none =>
                                    rw [decodeFixedLiteralSymFast9_none br
                                        ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                        (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                        (Or.inr hr7) hmod8 (Or.inl hr8) (Or.inr hr9)]
                                    rw [decodeFixedLiteralSym_none br bits7 bit8 bit9 br7 br8 br9
                                        h7 hslow7 (Or.inr hr7) h1on7 hslow1 (Or.inl hr8)
                                        h1on8 hslow1' (Or.inr hr9)]
                                | some sym9 =>
                                    rw [decodeFixedLiteralSymFast9_row9 br sym9
                                        ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                        (bits7 ||| (bit8 <<< 7)) br9
                                        h9 hfast9 hmod7 (Or.inr hr7) hmod8 (Or.inl hr8) hr9]
                                    rw [decodeFixedLiteralSym_row9_dis br sym9 bits7 bit8 bit9
                                        br7 br8 br9 h7 hslow7 (Or.inr hr7) h1on7 hslow1
                                        (Or.inl hr8) h1on8 hslow1' hr9]
                        | some o8 =>
                            cases o8 with
                            | none =>
                                cases hr9 : fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? with
                                | none =>
                                    rw [decodeFixedLiteralSymFast9_none br
                                        ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                        (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                        (Or.inr hr7) hmod8 (Or.inr hr8) (Or.inl hr9)]
                                    rw [decodeFixedLiteralSym_none br bits7 bit8 bit9 br7 br8 br9
                                        h7 hslow7 (Or.inr hr7) h1on7 hslow1 (Or.inr hr8)
                                        h1on8 hslow1' (Or.inl hr9)]
                                | some o9 =>
                                    cases o9 with
                                    | none =>
                                        rw [decodeFixedLiteralSymFast9_none br
                                            ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                            (bits7 ||| (bit8 <<< 7)) br9 h9 hfast9 hmod7
                                            (Or.inr hr7) hmod8 (Or.inr hr8) (Or.inr hr9)]
                                        rw [decodeFixedLiteralSym_none br bits7 bit8 bit9
                                            br7 br8 br9 h7 hslow7 (Or.inr hr7) h1on7 hslow1
                                            (Or.inr hr8) h1on8 hslow1' (Or.inr hr9)]
                                    | some sym9 =>
                                        rw [decodeFixedLiteralSymFast9_row9 br sym9
                                            ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                            (bits7 ||| (bit8 <<< 7)) br9
                                            h9 hfast9 hmod7 (Or.inr hr7) hmod8 (Or.inr hr8) hr9]
                                        rw [decodeFixedLiteralSym_row9_dis br sym9 bits7 bit8 bit9
                                            br7 br8 br9 h7 hslow7 (Or.inr hr7) h1on7 hslow1
                                            (Or.inr hr8) h1on8 hslow1' hr9]
                            | some sym8 =>
                                rw [decodeFixedLiteralSymFast9_row8 br sym8
                                    ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7
                                    (bits7 ||| (bit8 <<< 7)) br9 br8
                                    h9 hfast9 hmod7 (Or.inr hr7) hmod8 hr8 h8 hfast8]
                                rw [decodeFixedLiteralSym_row8_dis br sym8 bits7 bit8 br7 br8
                                    h7 hslow7 (Or.inr hr7) h1on7 hslow1 hr8]
                    | some sym7 =>
                        rw [decodeFixedLiteralSymFast9_row7 br sym7
                            ((bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)) bits7 br9 br7
                            h9 hfast9 hmod7 hr7 h7 hfast7]
                        rw [decodeFixedLiteralSym_row7 br sym7 bits7 br7 h7 hslow7 hr7]
  · -- 9 bits NOT available: fast falls back to slow directly.
    unfold decodeFixedLiteralSymFast9
    rw [dif_neg h9]

end Png

end Bitmaps
