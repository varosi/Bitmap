import Bitmap.Lemmas.Png.Core
import Bitmap.Png
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.ByteArray.Lemmas
import Init.Data.Range.Lemmas
import Init.Data.UInt.Lemmas
import Batteries.Data.ByteArray

universe u

namespace Bitmaps

namespace Png

lemma shiftLeft_bit (b : Bool) (res n : Nat) :
    (Nat.bit b res) <<< n = (res <<< (n + 1)) + (b.toNat <<< n) := by
  -- Expand `bit` and shift-left as multiplication.
  have hbit : Nat.bit b res = 2 * res + b.toNat := by
    simpa using (Nat.bit_val b res)
  calc
    (Nat.bit b res) <<< n
        = (2 * res + b.toNat) * 2 ^ n := by
            simp [hbit, Nat.shiftLeft_eq]
    _ = (2 * res) * 2 ^ n + b.toNat * 2 ^ n := by
            simp [Nat.add_mul]
    _ = res * 2 ^ (n + 1) + b.toNat * 2 ^ n := by
            simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]
    _ = (res <<< (n + 1)) + (b.toNat <<< n) := by
            simp [Nat.shiftLeft_eq]

lemma reverseBitsAux_eq_add (code len res : Nat) :
    reverseBitsAux code len res = reverseBits code len + (res <<< len) := by
  induction len generalizing code res with
  | zero =>
      simp [reverseBits, reverseBitsAux]
  | succ n ih =>
      have hbit : Nat.bit (code.testBit 0) res = 2 * res + (code.testBit 0).toNat := by
        simpa using (Nat.bit_val (code.testBit 0) res)
      calc
        reverseBitsAux code (n + 1) res
            = reverseBitsAux (code >>> 1) n (Nat.bit (code.testBit 0) res) := by
                simp [reverseBitsAux]
        _ = reverseBits (code >>> 1) n + ((Nat.bit (code.testBit 0) res) <<< n) := by
                exact (ih (code := code >>> 1) (res := Nat.bit (code.testBit 0) res))
        _ = reverseBits (code >>> 1) n + ((res <<< (n + 1)) + ((code.testBit 0).toNat <<< n)) := by
                simp [shiftLeft_bit, Nat.add_assoc, Nat.add_comm]
        _ = (reverseBits (code >>> 1) n + ((code.testBit 0).toNat <<< n)) + (res <<< (n + 1)) := by
                omega
        _ = reverseBits code (n + 1) + (res <<< (n + 1)) := by
                -- Expand `reverseBits` one step and use the auxiliary lemma with `res = 0`.
                have hrev :
                    reverseBits code (n + 1) =
                      reverseBits (code >>> 1) n + ((code.testBit 0).toNat <<< n) := by
                  calc
                    reverseBits code (n + 1)
                        = reverseBitsAux (code >>> 1) n (Nat.bit (code.testBit 0) 0) := by
                            simp [reverseBits, reverseBitsAux]
                    _ = reverseBits (code >>> 1) n + ((Nat.bit (code.testBit 0) 0) <<< n) := by
                            simpa using (ih (code := code >>> 1) (res := Nat.bit (code.testBit 0) 0))
                    _ = reverseBits (code >>> 1) n + ((code.testBit 0).toNat <<< n) := by
                            simp [Nat.bit_val, Nat.shiftLeft_eq]
                simp [hrev, Nat.add_comm]

lemma reverseBits_succ (code n : Nat) :
    reverseBits code (n + 1) =
      reverseBits (code >>> 1) n + ((code.testBit 0).toNat <<< n) := by
  calc
    reverseBits code (n + 1)
        = reverseBitsAux (code >>> 1) n (Nat.bit (code.testBit 0) 0) := by
            simp [reverseBits, reverseBitsAux]
    _ = reverseBits (code >>> 1) n + ((Nat.bit (code.testBit 0) 0) <<< n) := by
            exact (reverseBitsAux_eq_add (code := code >>> 1) (len := n) (res := Nat.bit (code.testBit 0) 0))
    _ = reverseBits (code >>> 1) n + ((code.testBit 0).toNat <<< n) := by
            simp [Nat.bit_val, Nat.shiftLeft_eq]

lemma reverseBits_lt (code len : Nat) : reverseBits code len < 2 ^ len := by
  induction len generalizing code with
  | zero =>
      simp [reverseBits, reverseBitsAux]
  | succ n ih =>
      have hfirst : reverseBits (code >>> 1) n < 2 ^ n := ih _
      have hbit : (code.testBit 0).toNat ≤ 1 := by
        cases h : code.testBit 0 <;> simp
      have hsecond : (code.testBit 0).toNat <<< n ≤ 2 ^ n := by
        -- shift-left by `n` is multiplication by `2^n`.
        simpa [Nat.shiftLeft_eq] using
          (Nat.mul_le_mul_right (2 ^ n) hbit)
      have hsum : reverseBits code (n + 1) < 2 ^ n + 2 ^ n := by
        have hdef := reverseBits_succ code n
        -- combine the bounds on the two summands
        calc
          reverseBits code (n + 1)
              = reverseBits (code >>> 1) n + ((code.testBit 0).toNat <<< n) := hdef
          _ < 2 ^ n + 2 ^ n := by
              exact Nat.add_lt_add_of_lt_of_le hfirst hsecond
      have hsum' : reverseBits code (n + 1) < 2 ^ n * 2 := by
        simpa [Nat.mul_two] using hsum
      -- `2^n * 2 = 2^(n+1)`
      simpa [Nat.pow_succ] using hsum'

lemma reverseBits_testBit (code len i : Nat) :
    (reverseBits code len).testBit i =
      if i < len then code.testBit (len - 1 - i) else false := by
  induction len generalizing code i with
  | zero =>
      simp [reverseBits, reverseBitsAux]
  | succ n ih =>
      by_cases hi : i < n + 1
      · have hrev :
          reverseBits code (n + 1) =
            2 ^ n * (code.testBit 0).toNat + reverseBits (code >>> 1) n := by
          calc
            reverseBits code (n + 1)
                = reverseBits (code >>> 1) n + ((code.testBit 0).toNat <<< n) := reverseBits_succ code n
            _ = reverseBits (code >>> 1) n + 2 ^ n * (code.testBit 0).toNat := by
                simp [Nat.shiftLeft_eq, Nat.mul_comm]
            _ = 2 ^ n * (code.testBit 0).toNat + reverseBits (code >>> 1) n := by
                simp [Nat.add_comm]
        have hb : reverseBits (code >>> 1) n < 2 ^ n := reverseBits_lt _ _
        have hbit :
            (reverseBits code (n + 1)).testBit i =
              if i < n then (reverseBits (code >>> 1) n).testBit i
              else (code.testBit 0).toNat.testBit (i - n) := by
          simpa [hrev] using
            (Nat.testBit_two_pow_mul_add
              (a := (code.testBit 0).toNat)
              (b := reverseBits (code >>> 1) n)
              (i := n)
              hb
              i)
        have hle : i ≤ n := Nat.le_of_lt_succ hi
        cases lt_or_eq_of_le hle with
        | inl hlt =>
            have hbit' : (reverseBits code (n + 1)).testBit i =
                (reverseBits (code >>> 1) n).testBit i := by
              simpa [hlt] using hbit
            have hih :
                (reverseBits (code >>> 1) n).testBit i =
                  if i < n then (code >>> 1).testBit (n - 1 - i) else false := ih _ _
            have hih' : (reverseBits (code >>> 1) n).testBit i =
                (code >>> 1).testBit (n - 1 - i) := by
              simpa [hlt] using hih
            have hshift :
                (code >>> 1).testBit (n - 1 - i) =
                  code.testBit ((n - 1 - i) + 1) := by
              simp [Nat.add_comm]
            have hcalc : (n - 1 - i) + 1 = n - i := by omega
            have hres :
                (reverseBits code (n + 1)).testBit i = code.testBit (n - i) := by
              calc
                (reverseBits code (n + 1)).testBit i
                    = (reverseBits (code >>> 1) n).testBit i := hbit'
                _ = (code >>> 1).testBit (n - 1 - i) := hih'
                _ = code.testBit ((n - 1 - i) + 1) := hshift
                _ = code.testBit (n - i) := by simp [hcalc]
            simpa [hi, hlt] using hres
        | inr hEq =>
            have hnot : ¬ i < n := by
              rw [hEq]
              exact Nat.lt_irrefl n
            have hbit' : (reverseBits code (n + 1)).testBit i =
                (code.testBit 0).toNat.testBit (i - n) := by
              simpa [hnot] using hbit
            have hbit'' : (reverseBits code (n + 1)).testBit n =
                (code.testBit 0).toNat.testBit 0 := by
              have hbit'' := hbit'
              rw [hEq] at hbit''
              rw [Nat.sub_self] at hbit''
              exact hbit''
            have hres : (reverseBits code (n + 1)).testBit n = code.testBit 0 := by
              cases hbit0 : code.testBit 0 <;> simp [hbit'', hbit0]
            simpa [hEq, hi] using hres
      · have hlt : reverseBits code (n + 1) < 2 ^ (n + 1) := reverseBits_lt code (n + 1)
        have hle : n + 1 ≤ i := Nat.le_of_not_gt hi
        have hpow : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_of_le (a := 2) (by decide) hle
        have hlt' : reverseBits code (n + 1) < 2 ^ i := lt_of_lt_of_le hlt hpow
        have hfalse : (reverseBits code (n + 1)).testBit i = false :=
          Nat.testBit_lt_two_pow hlt'
        simp [hi, hfalse]

-- Prefix of a reversed code corresponds to a shift of the original code.
lemma reverseBits_prefix_shift (code len k : Nat) (hcode : code < 2 ^ len) (hk : k ≤ len) :
    reverseBits ((reverseBits code len) % 2 ^ k) k = code >>> (len - k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have hki : k - 1 - i < k := by omega
    have hki' : k - 1 - i < len := by omega
    have hmod :
        ((reverseBits code len) % 2 ^ k).testBit (k - 1 - i) =
          (reverseBits code len).testBit (k - 1 - i) := by
      simp [Nat.testBit_mod_two_pow, hki]
    have hrev :
        (reverseBits code len).testBit (k - 1 - i) =
          code.testBit (len - 1 - (k - 1 - i)) := by
      have := reverseBits_testBit (code := code) (len := len) (i := k - 1 - i)
      simpa [hki'] using this
    have hcalc : len - 1 - (k - 1 - i) = len - k + i := by omega
    calc
      (reverseBits ((reverseBits code len) % 2 ^ k) k).testBit i
          = ((reverseBits code len) % 2 ^ k).testBit (k - 1 - i) := by
              have := reverseBits_testBit (code := (reverseBits code len) % 2 ^ k) (len := k) (i := i)
              simpa [hi] using this
      _ = (reverseBits code len).testBit (k - 1 - i) := hmod
      _ = code.testBit (len - 1 - (k - 1 - i)) := hrev
      _ = code.testBit (len - k + i) := by simp [hcalc]
      _ = (code >>> (len - k)).testBit i := by
              -- `testBit` of a shifted value moves the index by the shift.
              symm
              simp [Nat.add_comm]
  · have hge : k ≤ i := Nat.le_of_not_gt hi
    have hfalseL : (reverseBits ((reverseBits code len) % 2 ^ k) k).testBit i = false := by
      have := reverseBits_testBit (code := (reverseBits code len) % 2 ^ k) (len := k) (i := i)
      simpa [hi] using this
    have hpow : 2 ^ (len - k) * 2 ^ k = 2 ^ len := by
      have hlen : len - k + k = len := Nat.sub_add_cancel hk
      calc
        2 ^ (len - k) * 2 ^ k = 2 ^ ((len - k) + k) := by
          symm
          simp [Nat.pow_add, Nat.mul_comm]
        _ = 2 ^ len := by simp [hlen]
    have hcode' : code < 2 ^ (len - k) * 2 ^ k := by
      simpa [hpow] using hcode
    have hdiv : code / 2 ^ (len - k) < 2 ^ k := Nat.div_lt_of_lt_mul hcode'
    have hlt : code >>> (len - k) < 2 ^ k := by
      simpa [Nat.shiftRight_eq_div_pow] using hdiv
    have hpow' : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_of_le (a := 2) (by decide) hge
    have hlt' : code >>> (len - k) < 2 ^ i := lt_of_lt_of_le hlt hpow'
    have hfalseR : (code >>> (len - k)).testBit i = false := Nat.testBit_lt_two_pow hlt'
    simp [hfalseL, hfalseR]

lemma reverseBits_reverseBits (code len : Nat) (hcode : code < 2 ^ len) :
    reverseBits (reverseBits code len) len = code := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < len
  · have h1 := reverseBits_testBit (code := reverseBits code len) (len := len) (i := i)
    have h2 := reverseBits_testBit (code := code) (len := len) (i := len - 1 - i)
    have hlen : len - 1 - i < len := by
      have : i ≤ len - 1 := by omega
      omega
    -- simplify the nested testBit
    have h1' :
        (reverseBits (reverseBits code len) len).testBit i =
          (reverseBits code len).testBit (len - 1 - i) := by
      have h1' := h1
      simp [hi] at h1'
      exact h1'
    have h2' :
        (reverseBits code len).testBit (len - 1 - i) =
          code.testBit (len - 1 - (len - 1 - i)) := by
      have h2' := h2
      simp [hlen] at h2'
      exact h2'
    have hcalc : len - 1 - (len - 1 - i) = i := by omega
    calc
      (reverseBits (reverseBits code len) len).testBit i
          = (reverseBits code len).testBit (len - 1 - i) := h1'
      _ = code.testBit (len - 1 - (len - 1 - i)) := h2'
      _ = code.testBit i := by simp [hcalc]
  · have hle : len ≤ i := Nat.le_of_not_gt hi
    have hpow : 2 ^ len ≤ 2 ^ i := Nat.pow_le_pow_of_le (a := 2) (by decide) hle
    have hlt1 : reverseBits (reverseBits code len) len < 2 ^ len := reverseBits_lt _ _
    have hlt1' : reverseBits (reverseBits code len) len < 2 ^ i := lt_of_lt_of_le hlt1 hpow
    have hfalse1 : (reverseBits (reverseBits code len) len).testBit i = false :=
      Nat.testBit_lt_two_pow hlt1'
    have hfalse2 : code.testBit i = false := by
      have hlt' : code < 2 ^ i := lt_of_lt_of_le hcode hpow
      exact Nat.testBit_lt_two_pow hlt'
    simp [hfalse1, hfalse2]

lemma fixedLitLenRow7_size : fixedLitLenRow7.size = 1 <<< 7 := by
  simp [fixedLitLenRow7]

lemma fixedLitLenRow8_size : fixedLitLenRow8.size = 1 <<< 8 := by
  simp [fixedLitLenRow8]

lemma fixedLitLenRow9_size : fixedLitLenRow9.size = 1 <<< 9 := by
  simp [fixedLitLenRow9]

lemma fixedLitLenRow7_get (code : Nat) (hcode : code < 24) :
    fixedLitLenRow7[reverseBits code 7]'(by
      simpa [fixedLitLenRow7_size, Nat.shiftLeft_eq] using (reverseBits_lt code 7)) =
      some (256 + code) := by
  have hcode7 : code < 2 ^ 7 := by
    have : 24 ≤ 2 ^ 7 := by decide
    exact lt_of_lt_of_le hcode this
  have hrev : reverseBits (reverseBits code 7) 7 = code :=
    reverseBits_reverseBits code 7 hcode7
  -- unfold the row and simplify
  simp [fixedLitLenRow7, hrev, hcode]

lemma fixedLitLenRow8_get_low (code : Nat) (h48 : 48 ≤ code) (hcode : code < 192) :
    fixedLitLenRow8[reverseBits code 8]'(by
      simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using (reverseBits_lt code 8)) =
      some (code - 48) := by
  have hcode8 : code < 2 ^ 8 := by
    have : 192 ≤ 2 ^ 8 := by decide
    exact lt_of_lt_of_le hcode this
  have hrev : reverseBits (reverseBits code 8) 8 = code :=
    reverseBits_reverseBits code 8 hcode8
  have hget :
      fixedLitLenRow8[reverseBits code 8]'(by
        simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using (reverseBits_lt code 8)) =
        let code := reverseBits (reverseBits code 8) 8
        if code < 192 then
          if 48 ≤ code then some (code - 48) else none
        else if code < 200 then some (code - 192 + 280) else none := by
      simp [fixedLitLenRow8]
  have hget' := hget
  rw [hrev] at hget'
  simp [hcode, h48] at hget'
  exact hget'

lemma fixedLitLenRow8_get_high (code : Nat) (h192 : 192 ≤ code) (hcode : code < 200) :
    fixedLitLenRow8[reverseBits code 8]'(by
      simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using (reverseBits_lt code 8)) =
      some (code - 192 + 280) := by
  have hcode8 : code < 2 ^ 8 := by
    have : 200 ≤ 2 ^ 8 := by decide
    exact lt_of_lt_of_le hcode this
  have hrev : reverseBits (reverseBits code 8) 8 = code :=
    reverseBits_reverseBits code 8 hcode8
  have hnot : ¬ code < 192 := Nat.not_lt_of_ge h192
  have hget :
      fixedLitLenRow8[reverseBits code 8]'(by
        simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using (reverseBits_lt code 8)) =
        let code := reverseBits (reverseBits code 8) 8
        if code < 192 then
          if 48 ≤ code then some (code - 48) else none
        else if code < 200 then some (code - 192 + 280) else none := by
      simp [fixedLitLenRow8]
  have hget' := hget
  rw [hrev] at hget'
  simp [hcode, hnot] at hget'
  exact hget'

lemma fixedLitLenRow9_get (code : Nat) (h400 : 400 ≤ code) (hcode : code < 512) :
    fixedLitLenRow9[reverseBits code 9]'(by
      simpa [fixedLitLenRow9_size, Nat.shiftLeft_eq] using (reverseBits_lt code 9)) =
      some (code - 400 + 144) := by
  have hcode9 : code < 2 ^ 9 := by
    have : 512 ≤ 2 ^ 9 := by decide
    exact lt_of_lt_of_le hcode this
  have hrev : reverseBits (reverseBits code 9) 9 = code :=
    reverseBits_reverseBits code 9 hcode9
  have hget :
      fixedLitLenRow9[reverseBits code 9]'(by
        simpa [fixedLitLenRow9_size, Nat.shiftLeft_eq] using (reverseBits_lt code 9)) =
        let code := reverseBits (reverseBits code 9) 9
        if 400 ≤ code then some (code - 400 + 144) else none := by
    simp [fixedLitLenRow9]
  have hget' := hget
  rw [hrev] at hget'
  simp [h400] at hget'
  exact hget'

lemma fixedLitLenRow7_get_none_of_ge (bits : Nat) (hbits : bits < fixedLitLenRow7.size)
    (h24 : 24 ≤ reverseBits bits 7) :
    fixedLitLenRow7[bits]'hbits = none := by
  have hnot : ¬ reverseBits bits 7 < 24 := Nat.not_lt_of_ge h24
  simp [fixedLitLenRow7, hnot]

set_option maxRecDepth 2048 in
lemma fixedLitLenRow8_get_none_of_ge (bits : Nat) (hbits : bits < fixedLitLenRow8.size)
    (h200 : 200 ≤ reverseBits bits 8) :
    fixedLitLenRow8[bits]'hbits = none := by
  classical
  have hnot192 : ¬ reverseBits bits 8 < 192 := by
    exact Nat.not_lt_of_ge (le_trans (by decide : 192 ≤ 200) h200)
  have hnot200 : ¬ reverseBits bits 8 < 200 := Nat.not_lt_of_ge h200
  simp [fixedLitLenRow8, hnot192, hnot200]

lemma fixedLitLenCode_row_lo (sym : Nat) (hsym : sym ≤ 143) :
    fixedLitLenRow8[reverseBits (sym + 48) 8]'(by
      simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using (reverseBits_lt (sym + 48) 8)) =
      some sym := by
  have h48 : 48 ≤ sym + 48 := by omega
  have hcode : sym + 48 < 192 := by omega
  simpa [Nat.add_sub_cancel_left] using
    (fixedLitLenRow8_get_low (code := sym + 48) h48 hcode)

lemma fixedLitLenCode_row_mid (sym : Nat) (hsym : 144 ≤ sym) (hsym' : sym ≤ 255) :
    fixedLitLenRow9[reverseBits (sym - 144 + 400) 9]'(by
      simpa [fixedLitLenRow9_size, Nat.shiftLeft_eq] using
        (reverseBits_lt (sym - 144 + 400) 9)) =
      some sym := by
  have h400 : 400 ≤ sym - 144 + 400 := by omega
  have hcode : sym - 144 + 400 < 512 := by omega
  have hrow := fixedLitLenRow9_get (code := sym - 144 + 400) h400 hcode
  have hcalc1 : sym - 144 + 400 - 400 + 144 = sym - 144 + 144 := by omega
  have hcalc2 : sym - 144 + 144 = sym := Nat.sub_add_cancel hsym
  simpa [hcalc1, hcalc2] using hrow

lemma fixedLitLenCode_row_hi (sym : Nat) (hsym : 256 ≤ sym) (hsym' : sym ≤ 279) :
    fixedLitLenRow7[reverseBits (sym - 256) 7]'(by
      simpa [fixedLitLenRow7_size, Nat.shiftLeft_eq] using (reverseBits_lt (sym - 256) 7)) =
      some sym := by
  have hcode : sym - 256 < 24 := by omega
  have hrow := fixedLitLenRow7_get (code := sym - 256) hcode
  have hcalc : 256 + (sym - 256) = sym := by omega
  simpa [hcalc] using hrow

lemma fixedLitLenCode_row_hi2 (sym : Nat) (hsym : 280 ≤ sym) (hsym' : sym ≤ 287) :
    fixedLitLenRow8[reverseBits (sym - 280 + 192) 8]'(by
      simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using
        (reverseBits_lt (sym - 280 + 192) 8)) =
      some sym := by
  have h192 : 192 ≤ sym - 280 + 192 := by omega
  have hcode : sym - 280 + 192 < 200 := by omega
  have hrow := fixedLitLenRow8_get_high (code := sym - 280 + 192) h192 hcode
  have hcalc1 : sym - 280 + 192 - 192 + 280 = sym - 280 + 280 := by omega
  have hcalc2 : sym - 280 + 280 = sym := Nat.sub_add_cancel hsym
  simpa [hcalc1, hcalc2] using hrow

lemma fixedLitLenCode_lo (sym : Nat) (hsym : sym ≤ 143) :
    fixedLitLenCode sym = (sym + 48, 8) := by
  simp [fixedLitLenCode, hsym]

lemma fixedLitLenCode_mid (sym : Nat) (hsym : 144 ≤ sym) (hsym' : sym ≤ 255) :
    fixedLitLenCode sym = (sym - 144 + 400, 9) := by
  have hnot : ¬ sym ≤ 143 := by omega
  simp [fixedLitLenCode, hnot, hsym']

lemma fixedLitLenCode_hi (sym : Nat) (hsym : 256 ≤ sym) (hsym' : sym ≤ 279) :
    fixedLitLenCode sym = (sym - 256, 7) := by
  have hnot : ¬ sym ≤ 255 := by omega
  have hnot' : ¬ sym ≤ 143 := by omega
  simp [fixedLitLenCode, hnot', hnot, hsym']

lemma fixedLitLenCode_hi2 (sym : Nat) (hsym : 280 ≤ sym) (hsym' : sym ≤ 287) :
    fixedLitLenCode sym = (sym - 280 + 192, 8) := by
  have hnot : ¬ sym ≤ 279 := by omega
  have hnot' : ¬ sym ≤ 255 := by omega
  have hnot'' : ¬ sym ≤ 143 := by omega
  simp [fixedLitLenCode, hnot'', hnot', hnot]

lemma fixedLitLenCode_len_pos (sym : Nat) (hsym : sym < 288) :
    1 ≤ (fixedLitLenCode sym).2 := by
  by_cases h143 : sym ≤ 143
  · have h := fixedLitLenCode_lo sym h143
    simp [h]
  · have h144 : 144 ≤ sym := by omega
    by_cases h255 : sym ≤ 255
    · have h := fixedLitLenCode_mid sym h144 h255
      simp [h]
    · have h256 : 256 ≤ sym := by omega
      by_cases h279 : sym ≤ 279
      · have h := fixedLitLenCode_hi sym h256 h279
        simp [h]
      · have h280 : 280 ≤ sym := by omega
        have h := fixedLitLenCode_hi2 sym h280 (by omega)
        simp [h]

-- Decoding a fixed literal/length symbol after writing its fixed code.
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096
lemma decodeFixedLiteralSym_row7 (br : BitReader) (sym bits7 : Nat) (br7 : BitReader)
    (hread7 : br.bitIndex + 7 ≤ br.data.size * 8)
    (hbits7 : br.readBits 7 hread7 = (bits7, br7))
    (hrow7 : fixedLitLenRow7[bits7]? = some (some sym)) :
    decodeFixedLiteralSym br = some (sym, br7) := by
  unfold decodeFixedLiteralSym
  by_cases h : br.bitIndex + 7 ≤ br.data.size * 8
  · have hbits7' : br.readBits 7 h = (bits7, br7) := by
      calc
        br.readBits 7 h = br.readBits 7 hread7 := by
          exact readBits_proof_irrel (br := br) (n := 7) (h1 := h) (h2 := hread7)
        _ = (bits7, br7) := hbits7
    simp [h, hbits7', hrow7]
  · cases h hread7

lemma decodeFixedLiteralSym_row8 (br : BitReader) (sym bits7 bit8 : Nat) (br7 br8 : BitReader)
    (hread7 : br.bitIndex + 7 ≤ br.data.size * 8)
    (hbits7 : br.readBits 7 hread7 = (bits7, br7))
    (hrow7 : fixedLitLenRow7[bits7]? = some none)
    (hread1 : br7.bitIndex + 1 ≤ br7.data.size * 8)
    (hbits8 : br7.readBits 1 hread1 = (bit8, br8))
    (hrow8 : fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? = some (some sym)) :
    decodeFixedLiteralSym br = some (sym, br8) := by
  unfold decodeFixedLiteralSym
  by_cases h : br.bitIndex + 7 ≤ br.data.size * 8
  · have hbits7' : br.readBits 7 h = (bits7, br7) := by
      calc
        br.readBits 7 h = br.readBits 7 hread7 := by
          exact readBits_proof_irrel (br := br) (n := 7) (h1 := h) (h2 := hread7)
        _ = (bits7, br7) := hbits7
    by_cases h1 : br7.bitIndex + 1 ≤ br7.data.size * 8
    · have hbits8' : br7.readBits 1 h1 = (bit8, br8) := by
        calc
          br7.readBits 1 h1 = br7.readBits 1 hread1 := by
            exact readBits_proof_irrel (br := br7) (n := 1) (h1 := h1) (h2 := hread1)
          _ = (bit8, br8) := hbits8
      simp [h, hbits7', hrow7, h1, hbits8', hrow8]
    · cases h1 hread1
  · cases h hread7

lemma decodeFixedLiteralSym_row9 (br : BitReader) (sym bits7 bit8 bit9 : Nat) (br7 br8 br9 : BitReader)
    (hread7 : br.bitIndex + 7 ≤ br.data.size * 8)
    (hbits7 : br.readBits 7 hread7 = (bits7, br7))
    (hrow7 : fixedLitLenRow7[bits7]? = some none)
    (hread1 : br7.bitIndex + 1 ≤ br7.data.size * 8)
    (hbits8 : br7.readBits 1 hread1 = (bit8, br8))
    (hrow8 : fixedLitLenRow8[bits7 ||| (bit8 <<< 7)]? = some none)
    (hread1' : br8.bitIndex + 1 ≤ br8.data.size * 8)
    (hbits9 : br8.readBits 1 hread1' = (bit9, br9))
    (hrow9 : fixedLitLenRow9[(bits7 ||| (bit8 <<< 7)) ||| (bit9 <<< 8)]? = some (some sym)) :
    decodeFixedLiteralSym br = some (sym, br9) := by
  unfold decodeFixedLiteralSym
  by_cases h : br.bitIndex + 7 ≤ br.data.size * 8
  · have hbits7' : br.readBits 7 h = (bits7, br7) := by
      calc
        br.readBits 7 h = br.readBits 7 hread7 := by
          exact readBits_proof_irrel (br := br) (n := 7) (h1 := h) (h2 := hread7)
        _ = (bits7, br7) := hbits7
    by_cases h1 : br7.bitIndex + 1 ≤ br7.data.size * 8
    · have hbits8' : br7.readBits 1 h1 = (bit8, br8) := by
        calc
          br7.readBits 1 h1 = br7.readBits 1 hread1 := by
            exact readBits_proof_irrel (br := br7) (n := 1) (h1 := h1) (h2 := hread1)
          _ = (bit8, br8) := hbits8
      by_cases h2 : br8.bitIndex + 1 ≤ br8.data.size * 8
      · have hbits9' : br8.readBits 1 h2 = (bit9, br9) := by
          calc
            br8.readBits 1 h2 = br8.readBits 1 hread1' := by
              exact readBits_proof_irrel (br := br8) (n := 1) (h1 := h2) (h2 := hread1')
            _ = (bit9, br9) := hbits9
        simp [h, hbits7', hrow7, h1, hbits8', hrow8, h2, hbits9', hrow9]
      · cases h2 hread1'
    · cases h1 hread1
  · cases h hread7

lemma decodeFixedLiteralSym_readerAt_writeBits_len8_core (bw : BitWriter) (sym : Nat) (restBits restLen code : Nat)
    (hrow7 : fixedLitLenRow7[(reverseBits code 8 ||| (restBits <<< 8)) % 2 ^ 7]? = some none)
    (hrow8 : fixedLitLenRow8[(reverseBits code 8 ||| (restBits <<< 8)) % 2 ^ 8]? = some (some sym))
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bits := reverseBits code 8
    let bitsTot := bits ||| (restBits <<< 8)
    let lenTot := 8 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot 8) bw'.flush
          (by
            have hk : 8 ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot 8 hbit)) := by
  let bits := reverseBits code 8
  let bitsTot := bits ||| (restBits <<< 8)
  let lenTot := 8 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br7 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 7) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 7 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  have hread7 : br.bitIndex + 7 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7) (hk := by omega) hbit)
  have hbits7 :
      br.readBits 7 hread7 =
        (bitsTot % 2 ^ 7, br7) := by
    simpa [br, bw', lenTot] using
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hsplit :
      BitWriter.writeBits bw bitsTot 8 =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1 := by
    simpa using (writeBits_split bw bitsTot 7 1)
  have hsplit7 :
      BitWriter.writeBits bw bitsTot lenTot =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) (lenTot - 7) := by
    have hk : 7 ≤ lenTot := by omega
    simpa [Nat.add_comm, Nat.sub_add_cancel hk, lenTot] using
      (writeBits_split bw bitsTot 7 (lenTot - 7))
  have hread1 :
      br7.bitIndex + 1 ≤ br7.data.size * 8 := by
    have hread1' :=
      (readerAt_writeBits_bound
        (bw := BitWriter.writeBits bw bitsTot 7) (bits := bitsTot >>> 7) (len := lenTot - 7) (k := 1)
        (hk := by omega)
        (hbit := bitPos_lt_8_writeBits bw bitsTot 7 hbit))
    simpa [bw', hsplit7, br7, lenTot] using hread1'
  let br8 :=
    BitWriter.readerAt
      (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1) bw'.flush
      (by
        have h :=
          flush_size_writeBits_prefix (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1 (lenTot - 7)
            (by omega)
        simpa [bw', hsplit7] using h)
      (bitPos_lt_8_writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1
        (bitPos_lt_8_writeBits bw bitsTot 7 hbit))
  have hbits8 :
      br7.readBits 1 hread1 = ((bitsTot >>> 7) % 2, br8) := by
    simpa [bw', hsplit7, br7, br8, lenTot] using
        (readBits_readerAt_writeBits_prefix (bw := BitWriter.writeBits bw bitsTot 7)
          (bits := bitsTot >>> 7) (len := lenTot - 7) (k := 1) (hk := by omega)
          (hbit := bitPos_lt_8_writeBits bw bitsTot 7 hbit)
          (hcur := curClearAbove_writeBits bw bitsTot 7 hbit hcur))
  have hbits8_eq :
      (bitsTot % 2 ^ 7) ||| (((bitsTot >>> 7) % 2) <<< 7) = bitsTot % 2 ^ 8 := by
    simpa using (mod_two_pow_decomp_high bitsTot 7).symm
  have hrow8' :
      fixedLitLenRow8[(bitsTot % 2 ^ 7) ||| (((bitsTot >>> 7) % 2) <<< 7)]? = some (some sym) := by
    simpa [hbits8_eq] using hrow8
  have hresult :
      decodeFixedLiteralSym br = some (sym, br8) := by
    exact decodeFixedLiteralSym_row8 (br := br) (sym := sym) (bits7 := bitsTot % 2 ^ 7)
      (bit8 := (bitsTot >>> 7) % 2) (br7 := br7) (br8 := br8)
      hread7 hbits7 hrow7 hread1 hbits8 hrow8'
  have hbw' :
      BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1 =
        BitWriter.writeBits bw bitsTot 8 := by
    simp [hsplit]
  simpa [bits, bitsTot, lenTot, bw', br, br8, hbw'] using hresult

lemma decodeFixedLiteralSym_readerAt_writeBits_len9_core (bw : BitWriter) (sym : Nat) (restBits restLen code : Nat)
    (hrow7 : fixedLitLenRow7[(reverseBits code 9 ||| (restBits <<< 9)) % 2 ^ 7]? = some none)
    (hrow8 : fixedLitLenRow8[(reverseBits code 9 ||| (restBits <<< 9)) % 2 ^ 8]? = some none)
    (hrow9 : fixedLitLenRow9[(reverseBits code 9 ||| (restBits <<< 9)) % 2 ^ 9]? = some (some sym))
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bits := reverseBits code 9
    let bitsTot := bits ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot 9) bw'.flush
          (by
            have hk : 9 ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot 9 hbit)) := by
  let bits := reverseBits code 9
  let bitsTot := bits ||| (restBits <<< 9)
  let lenTot := 9 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br7 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 7) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 7 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  have hread7 : br.bitIndex + 7 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7) (hk := by omega) hbit)
  have hbits7 :
      br.readBits 7 hread7 =
        (bitsTot % 2 ^ 7, br7) := by
    simpa [br, bw', lenTot] using
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hsplit8 :
      BitWriter.writeBits bw bitsTot 8 =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1 := by
    simpa using (writeBits_split bw bitsTot 7 1)
  have hsplit7_2 :
      BitWriter.writeBits bw bitsTot 9 =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 2 := by
    simpa using (writeBits_split bw bitsTot 7 2)
  have hsplit7 :
      BitWriter.writeBits bw bitsTot lenTot =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) (lenTot - 7) := by
    have hk : 7 ≤ lenTot := by omega
    simpa [Nat.add_comm, Nat.sub_add_cancel hk, lenTot] using
      (writeBits_split bw bitsTot 7 (lenTot - 7))
  have hread1 :
      br7.bitIndex + 1 ≤ br7.data.size * 8 := by
    have hread1' :=
      (readerAt_writeBits_bound
        (bw := BitWriter.writeBits bw bitsTot 7) (bits := bitsTot >>> 7) (len := lenTot - 7) (k := 1)
        (hk := by omega)
        (hbit := bitPos_lt_8_writeBits bw bitsTot 7 hbit))
    simpa [bw', hsplit7, br7, lenTot] using hread1'
  let br8 :=
    BitWriter.readerAt
      (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1) bw'.flush
      (by
        have h :=
          flush_size_writeBits_prefix (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1 (lenTot - 7)
            (by omega)
        simpa [bw', hsplit7] using h)
      (bitPos_lt_8_writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1
        (bitPos_lt_8_writeBits bw bitsTot 7 hbit))
  have hbits8 :
      br7.readBits 1 hread1 = ((bitsTot >>> 7) % 2, br8) := by
    simpa [bw', hsplit7, br7, br8, lenTot] using
        (readBits_readerAt_writeBits_prefix (bw := BitWriter.writeBits bw bitsTot 7)
          (bits := bitsTot >>> 7) (len := lenTot - 7) (k := 1) (hk := by omega)
          (hbit := bitPos_lt_8_writeBits bw bitsTot 7 hbit)
          (hcur := curClearAbove_writeBits bw bitsTot 7 hbit hcur))
  have hbits8_eq :
      (bitsTot % 2 ^ 7) ||| (((bitsTot >>> 7) % 2) <<< 7) = bitsTot % 2 ^ 8 := by
    simpa using (mod_two_pow_decomp_high bitsTot 7).symm
  have hrow8' :
      fixedLitLenRow8[(bitsTot % 2 ^ 7) ||| (((bitsTot >>> 7) % 2) <<< 7)]? = some none := by
    simpa [hbits8_eq] using hrow8
  have hsplit9 :
      BitWriter.writeBits bw bitsTot 9 =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 8) (bitsTot >>> 8) 1 := by
    simpa using (writeBits_split bw bitsTot 8 1)
  have hsplit8tot :
      BitWriter.writeBits bw bitsTot lenTot =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 8) (bitsTot >>> 8) (lenTot - 8) := by
    have hk : 8 ≤ lenTot := by omega
    simpa [Nat.add_comm, Nat.sub_add_cancel hk, lenTot] using
      (writeBits_split bw bitsTot 8 (lenTot - 8))
  have hread2 :
      br8.bitIndex + 1 ≤ br8.data.size * 8 := by
    have hread2' :=
      (readerAt_writeBits_bound
        (bw := BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1)
        (bits := bitsTot >>> 8) (len := lenTot - 8) (k := 1) (hk := by omega)
        (hbit := bitPos_lt_8_writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1
          (bitPos_lt_8_writeBits bw bitsTot 7 hbit)))
    simpa [bw', hsplit8tot, br8, lenTot] using hread2'
  let br9 :=
    BitWriter.readerAt
      (BitWriter.writeBits (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1)
          (bitsTot >>> 8) 1) bw'.flush
      (by
        have h :=
          flush_size_writeBits_prefix
            (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1) (bitsTot >>> 8) 1
            (lenTot - 8) (by omega)
        simpa [bw', hsplit8tot] using h)
      (bitPos_lt_8_writeBits
        (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1) (bitsTot >>> 8) 1
        (bitPos_lt_8_writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1
          (bitPos_lt_8_writeBits bw bitsTot 7 hbit)))
  have hbits9 :
      br8.readBits 1 hread2 = ((bitsTot >>> 8) % 2, br9) := by
    simpa [bw', hsplit8tot, br8, br9, lenTot] using
      (readBits_readerAt_writeBits_prefix
        (bw := BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1)
        (bits := bitsTot >>> 8) (len := lenTot - 8) (k := 1) (hk := by omega)
        (hbit := bitPos_lt_8_writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1
          (bitPos_lt_8_writeBits bw bitsTot 7 hbit))
        (hcur := curClearAbove_writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1
          (bitPos_lt_8_writeBits bw bitsTot 7 hbit) (curClearAbove_writeBits bw bitsTot 7 hbit hcur)))
  have hbits9_eq :
      (bitsTot % 2 ^ 8) ||| (((bitsTot >>> 8) % 2) <<< 8) = bitsTot % 2 ^ 9 := by
    simpa using (mod_two_pow_decomp_high bitsTot 8).symm
  have hrow9' :
      fixedLitLenRow9[(bitsTot % 2 ^ 7) ||| (((bitsTot >>> 7) % 2) <<< 7) |||
        (((bitsTot >>> 8) % 2) <<< 8)]? = some (some sym) := by
    simpa [hbits8_eq, hbits9_eq] using hrow9
  have hresult :
      decodeFixedLiteralSym br = some (sym, br9) := by
    exact decodeFixedLiteralSym_row9 (br := br) (sym := sym) (bits7 := bitsTot % 2 ^ 7)
      (bit8 := (bitsTot >>> 7) % 2) (bit9 := (bitsTot >>> 8) % 2)
      (br7 := br7) (br8 := br8) (br9 := br9)
      hread7 hbits7 hrow7 hread1 hbits8 hrow8' hread2 hbits9 hrow9'
  have hbw9 :
      BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1) (bitsTot >>> 8) 1 =
        BitWriter.writeBits bw bitsTot 9 := by
    have hsplit8' : BitWriter.writeBits bw bitsTot 8 =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 7) (bitsTot >>> 7) 1 := by
      simpa using (writeBits_split bw bitsTot 7 1)
    have hsplit9' : BitWriter.writeBits bw bitsTot 9 =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot 8) (bitsTot >>> 8) 1 := by
      simpa using (writeBits_split bw bitsTot 8 1)
    simp [hsplit9', hsplit8']
  simpa [bits, bitsTot, lenTot, bw', br, br9, hbw9] using hresult

lemma decodeFixedLiteralSym_readerAt_writeBits_lo (bw : BitWriter) (sym : Nat) (restBits restLen : Nat)
    (h143 : sym ≤ 143) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hk : len ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)) := by
  have hcode : fixedLitLenCode sym = (sym + 48, 8) := fixedLitLenCode_lo sym h143
  let code := sym + 48
  let bits := reverseBits code 8
  let bitsTot := bits ||| (restBits <<< 8)
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 8 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode8 : code < 2 ^ 8 := by
    have hlt : code < 192 := by omega
    have hle : 192 ≤ 2 ^ 8 := by decide
    exact lt_of_lt_of_le hlt hle
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 8) (k := 7) hcode8 (by decide))
  have hrev7' : reverseBits (bitsTot % 2 ^ 7) 7 = code >>> 1 := by
    simpa [hbits7_eq] using hrev7
  have h24 : 24 ≤ code >>> 1 := by
    have hdiv : 24 ≤ code / 2 := by
      have h48 : 48 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 (by simpa [Nat.mul_comm] using h48)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by
      simpa [hrev7'] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7]
  have hbits8_eq' : bitsTot % 2 ^ 8 = bits := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hmod' : bits % 2 ^ 8 = bits := Nat.mod_eq_of_lt hlt
    have hmod := mod_two_pow_or_shift bits restBits 8 8 (by decide)
    simpa [bitsTot, hmod'] using hmod
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hlt' : bitsTot % 2 ^ 8 < 2 ^ 8 := by
      simpa [hbits8_eq', bitsTot] using hlt
    simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt'
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = some sym := by
    have hrow := fixedLitLenCode_row_lo (sym := sym) h143
    simpa [code, bits, hbits8_eq'] using hrow
  have hrow8? : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some (some sym) := by
    simp [hbits8_lt, hrow8]
  have h := decodeFixedLiteralSym_readerAt_writeBits_len8_core (bw := bw) (sym := sym)
      (restBits := restBits) (restLen := restLen) (code := code) hrow7? hrow8? hbit hcur
  simpa [hcode, code, bits, bitsTot] using h

lemma decodeFixedLiteralSym_readerAt_writeBits_mid (bw : BitWriter) (sym : Nat) (restBits restLen : Nat)
    (h144 : 144 ≤ sym) (h255 : sym ≤ 255) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hk : len ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)) := by
  have hcode : fixedLitLenCode sym = (sym - 144 + 400, 9) :=
    fixedLitLenCode_mid sym h144 h255
  let code := sym - 144 + 400
  let bits := reverseBits code 9
  let bitsTot := bits ||| (restBits <<< 9)
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 9 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode9 : code < 2 ^ 9 := by
    have hlt : code < 512 := by omega
    have hle : 512 ≤ 2 ^ 9 := by decide
    exact lt_of_lt_of_le hlt hle
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 2 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 9) (k := 7) hcode9 (by decide))
  have hrev7' : reverseBits (bitsTot % 2 ^ 7) 7 = code >>> 2 := by
    simpa [hbits7_eq] using hrev7
  have h24 : 24 ≤ code >>> 2 := by
    have hdiv : 24 ≤ code / 4 := by
      have h96 : 96 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (4 : Nat))).2 (by simpa [Nat.mul_comm] using h96)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by simpa [hrev7'] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7]
  have hbits8_eq' : bitsTot % 2 ^ 8 = bits % 2 ^ 8 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 8 9 (by decide))
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    simpa [hbits8_eq', fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt
  have hrev8 : reverseBits (bits % 2 ^ 8) 8 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 9) (k := 8) hcode9 (by decide))
  have hrev8' : reverseBits (bitsTot % 2 ^ 8) 8 = code >>> 1 := by
    simpa [hbits8_eq'] using hrev8
  have h200 : 200 ≤ code >>> 1 := by
    have hdiv : 200 ≤ code / 2 := by
      have h400 : 400 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 (by simpa [Nat.mul_comm] using h400)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = none := by
    have h200' : 200 ≤ reverseBits (bitsTot % 2 ^ 8) 8 := by simpa [hrev8'] using h200
    exact fixedLitLenRow8_get_none_of_ge (bits := bitsTot % 2 ^ 8) hbits8_lt h200'
  have hrow8? : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some none := by
    simp [hbits8_lt, hrow8]
  have hbits9_eq' : bitsTot % 2 ^ 9 = bits := by
    have hmod := mod_two_pow_or_shift bits restBits 9 9 (by decide)
    have hlt : bits < 2 ^ 9 := by simpa [bits] using (reverseBits_lt code 9)
    have hmod' : bits % 2 ^ 9 = bits := Nat.mod_eq_of_lt hlt
    simpa [bitsTot, hmod'] using hmod
  have hbits9_lt : bitsTot % 2 ^ 9 < fixedLitLenRow9.size := by
    have hlt : bits < 2 ^ 9 := by simpa [bits] using (reverseBits_lt code 9)
    simpa [hbits9_eq', fixedLitLenRow9_size, Nat.shiftLeft_eq] using hlt
  have hrow9 : fixedLitLenRow9[bitsTot % 2 ^ 9]'hbits9_lt = some sym := by
    have hrow := fixedLitLenCode_row_mid (sym := sym) h144 h255
    simpa [code, bits, hbits9_eq'] using hrow
  have hrow9? : fixedLitLenRow9[bitsTot % 2 ^ 9]? = some (some sym) := by
    simp [hbits9_lt, hrow9]
  have h := decodeFixedLiteralSym_readerAt_writeBits_len9_core (bw := bw) (sym := sym)
      (restBits := restBits) (restLen := restLen) (code := code) hrow7? hrow8? hrow9? hbit hcur
  simpa [hcode, code, bits, bitsTot] using h

lemma decodeFixedLiteralSym_readerAt_writeBits_hi (bw : BitWriter) (sym : Nat) (restBits restLen : Nat)
    (h256 : 256 ≤ sym) (h279 : sym ≤ 279) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hk : len ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)) := by
  have hcode : fixedLitLenCode sym = (sym - 256, 7) :=
    fixedLitLenCode_hi sym h256 h279
  let code := sym - 256
  let bits := reverseBits code 7
  let bitsTot := bits ||| (restBits <<< 7)
  let lenTot := 7 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br7 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 7) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 7 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  have hread7 : br.bitIndex + 7 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7) (hk := by omega) hbit)
  have hbits7 :
      br.readBits 7 hread7 =
        (bitsTot % 2 ^ 7, br7) := by
    simpa [br, bw', lenTot] using
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hbits7_eq : bitsTot % 2 ^ 7 = bits := by
    have hmod := mod_two_pow_or_shift bits restBits 7 7 (by decide)
    have hlt : bits < 2 ^ 7 := by simpa [bits] using (reverseBits_lt code 7)
    have hmod' : bits % 2 ^ 7 = bits := Nat.mod_eq_of_lt hlt
    simpa [bitsTot, hmod'] using hmod
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits < 2 ^ 7 := by simpa [bits] using (reverseBits_lt code 7)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = some sym := by
    have hrow := fixedLitLenCode_row_hi (sym := sym) h256 h279
    simpa [code, bits, hbits7_eq] using hrow
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some (some sym) := by
    simp [hbits7_lt, hrow7]
  have hresult :
      decodeFixedLiteralSym br = some (sym, br7) := by
    exact decodeFixedLiteralSym_row7 (br := br) (sym := sym) (bits7 := bitsTot % 2 ^ 7) (br7 := br7)
      hread7 hbits7 hrow7?
  simpa [hcode, code, bits, bitsTot, lenTot, bw', br, br7] using hresult

lemma decodeFixedLiteralSym_readerAt_writeBits_hi2 (bw : BitWriter) (sym : Nat) (restBits restLen : Nat)
    (h280 : 280 ≤ sym) (h287 : sym ≤ 287) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hk : len ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)) := by
  have hcode : fixedLitLenCode sym = (sym - 280 + 192, 8) :=
    fixedLitLenCode_hi2 sym h280 h287
  let code := sym - 280 + 192
  let bits := reverseBits code 8
  let bitsTot := bits ||| (restBits <<< 8)
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 8 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode8 : code < 2 ^ 8 := by
    have hlt : code < 200 := by omega
    have hle : 200 ≤ 2 ^ 8 := by decide
    exact lt_of_lt_of_le hlt hle
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 8) (k := 7) hcode8 (by decide))
  have hrev7' : reverseBits (bitsTot % 2 ^ 7) 7 = code >>> 1 := by
    simpa [hbits7_eq] using hrev7
  have h24 : 24 ≤ code >>> 1 := by
    have hdiv : 24 ≤ code / 2 := by
      have h48 : 48 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 (by simpa [Nat.mul_comm] using h48)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by simpa [hrev7'] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7]
  have hbits8_eq' : bitsTot % 2 ^ 8 = bits := by
    have hmod := mod_two_pow_or_shift bits restBits 8 8 (by decide)
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hmod' : bits % 2 ^ 8 = bits := Nat.mod_eq_of_lt hlt
    simpa [bitsTot, hmod'] using hmod
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    simpa [hbits8_eq', fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = some sym := by
    have hrow := fixedLitLenCode_row_hi2 (sym := sym) h280 h287
    simpa [code, bits, hbits8_eq'] using hrow
  have hrow8? : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some (some sym) := by
    simp [hbits8_lt, hrow8]
  have h := decodeFixedLiteralSym_readerAt_writeBits_len8_core (bw := bw) (sym := sym)
      (restBits := restBits) (restLen := restLen) (code := code) hrow7? hrow8? hbit hcur
  simpa [hcode, code, bits, bitsTot] using h

lemma decodeFixedLiteralSym_readerAt_writeBits (bw : BitWriter) (sym : Nat) (restBits restLen : Nat)
    (hsym : sym < 288) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hk : len ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)) := by
  classical
  by_cases h143 : sym ≤ 143
  · exact decodeFixedLiteralSym_readerAt_writeBits_lo (bw := bw) (sym := sym)
      (restBits := restBits) (restLen := restLen) h143 hbit hcur
  · have h144 : 144 ≤ sym := by omega
    by_cases h255 : sym ≤ 255
    · exact decodeFixedLiteralSym_readerAt_writeBits_mid (bw := bw) (sym := sym)
        (restBits := restBits) (restLen := restLen) h144 h255 hbit hcur
    · have h256 : 256 ≤ sym := by omega
      by_cases h279 : sym ≤ 279
      · exact decodeFixedLiteralSym_readerAt_writeBits_hi (bw := bw) (sym := sym)
          (restBits := restBits) (restLen := restLen) h256 h279 hbit hcur
      · have h280 : 280 ≤ sym := by omega
        have h287 : sym ≤ 287 := by omega
        exact decodeFixedLiteralSym_readerAt_writeBits_hi2 (bw := bw) (sym := sym)
          (restBits := restBits) (restLen := restLen) h280 h287 hbit hcur

-- Alias to avoid potential kernel resolution issues in later proofs.
lemma decodeFixedLiteralSym_readerAt_writeBits' (bw : BitWriter) (sym : Nat) (restBits restLen : Nat)
    (hsym : sym < 288) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSym br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hk : len ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)) := by
  simpa using (decodeFixedLiteralSym_readerAt_writeBits (bw := bw) (sym := sym)
    (restBits := restBits) (restLen := restLen) hsym hbit hcur)


-- Build a ByteArray by pushing the suffix of an Array.
end Png
end Bitmaps
