import Bitmap.Lemmas.Png.CoreByteArray

namespace Bitmaps

namespace Lemmas

namespace U32Helpers

open Png

/-- Big-endian 32-bit encoding always produces four bytes. -/
lemma u32be_size (n : Nat) : (u32be n).size = 4 := by
  have h : (u32be n).data.size = 4 := by
    simp [u32be]
  simpa [ByteArray.size_data] using h

/-- Reading a `u32be` slice recovers the original in-range natural number. -/
lemma readU32BE_u32be (n : Nat) (hn : n < 2 ^ 32) :
    readU32BE (u32be n) 0 (by simp [u32be_size]) = n := by
  have h0 : (n / 2 ^ 24) % 256 < UInt8.size := by
    have hlt : (n / 2 ^ 24) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256 : Nat))
    simpa [UInt8.size] using hlt
  have h1 : (n / 2 ^ 16) % 256 < UInt8.size := by
    have hlt : (n / 2 ^ 16) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256 : Nat))
    simpa [UInt8.size] using hlt
  have h2 : (n / 2 ^ 8) % 256 < UInt8.size := by
    have hlt : (n / 2 ^ 8) % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256 : Nat))
    simpa [UInt8.size] using hlt
  have h3 : n % 256 < UInt8.size := by
    have hlt : n % 256 < 256 := Nat.mod_lt _ (by decide : 0 < (256 : Nat))
    simpa [UInt8.size] using hlt
  have hb0 : (u32be n).get 0 (by simp [u32be_size]) = u8 ((n / 2 ^ 24) % 256) := by
    rfl
  have hb1 : (u32be n).get 1 (by simp [u32be_size]) = u8 ((n / 2 ^ 16) % 256) := by
    rfl
  have hb2 : (u32be n).get 2 (by simp [u32be_size]) = u8 ((n / 2 ^ 8) % 256) := by
    rfl
  have hb3 : (u32be n).get 3 (by simp [u32be_size]) = u8 (n % 256) := by
    rfl
  have hread :
      readU32BE (u32be n) 0 (by simp [u32be_size]) =
        ((n / 2 ^ 24) % 256) * 2 ^ 24 +
        ((n / 2 ^ 16) % 256) * 2 ^ 16 +
        ((n / 2 ^ 8) % 256) * 2 ^ 8 + n % 256 := by
    simp [readU32BE, hb0, hb1, hb2, hb3, u8,
      UInt8.toNat_ofNat_of_lt' h0, UInt8.toNat_ofNat_of_lt' h1,
      UInt8.toNat_ofNat_of_lt' h2, UInt8.toNat_ofNat_of_lt' h3,
      Nat.shiftLeft_eq, Nat.mul_comm]
  have h256 : (2 ^ 8 : Nat) = 256 := by decide
  have hpow : (2 ^ 24 : Nat) * 2 ^ 8 = 2 ^ 32 := by decide
  have h24lt : n / 2 ^ 24 < 2 ^ 8 := by
    apply Nat.div_lt_of_lt_mul
    simpa [hpow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn
  have h24mod : (n / 2 ^ 24) % 256 = n / 2 ^ 24 := by
    have : n / 2 ^ 24 < 256 := by simpa [h256] using h24lt
    exact Nat.mod_eq_of_lt this
  have h08 : n = (n / 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod n (2 ^ 8)).symm
  have h16 : n / 2 ^ 8 = (n / 2 ^ 8 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8 := by
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod (n / 2 ^ 8) (2 ^ 8)).symm
  have h24 : n / 2 ^ 16 = (n / 2 ^ 16 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8 := by
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod (n / 2 ^ 16) (2 ^ 8)).symm
  have hpow8 : (2 ^ 8 : Nat) * 2 ^ 8 = 2 ^ 16 := by decide
  have hpow16 : (2 ^ 8 : Nat) * 2 ^ 16 = 2 ^ 24 := by decide
  have hpow16' : (2 ^ 16 : Nat) * 2 ^ 8 = 2 ^ 24 := by decide
  have hmul_pow8 (a b : Nat) :
      (a * 2 ^ 8 + b) * 2 ^ 8 = a * 2 ^ 16 + b * 2 ^ 8 := by
    calc
      (a * 2 ^ 8 + b) * 2 ^ 8 = a * 2 ^ 8 * 2 ^ 8 + b * 2 ^ 8 := by
        simp [Nat.add_mul, Nat.mul_assoc]
      _ = a * 2 ^ 16 + b * 2 ^ 8 := by
        simp [Nat.mul_comm, Nat.mul_left_comm, hpow8]
  have hmul_pow16 (a b : Nat) :
      (a * 2 ^ 8 + b) * 2 ^ 16 = a * 2 ^ 24 + b * 2 ^ 16 := by
    calc
      (a * 2 ^ 8 + b) * 2 ^ 16 = a * 2 ^ 8 * 2 ^ 16 + b * 2 ^ 16 := by
        simp [Nat.add_mul, Nat.mul_assoc]
      _ = a * 2 ^ 24 + b * 2 ^ 16 := by
        simp [Nat.mul_assoc, hpow16]
  have hdiv16 : n / 2 ^ 8 / 2 ^ 8 = n / 2 ^ 16 := by
    simp [Nat.div_div_eq_div_mul, hpow8]
  have hdiv24 : n / 2 ^ 16 / 2 ^ 8 = n / 2 ^ 24 := by
    simp [Nat.div_div_eq_div_mul, hpow16']
  have hdecomp :
      (n / 2 ^ 24) * 2 ^ 24 +
        (n / 2 ^ 16 % 2 ^ 8) * 2 ^ 16 +
        (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 = n := by
    symm
    have h16' :
        (n / 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 =
          ((n / 2 ^ 8 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
      exact congrArg (fun t => t * 2 ^ 8 + n % 2 ^ 8) h16
    have h24' :
        (n / 2 ^ 16) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 =
          ((n / 2 ^ 16 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
      exact congrArg (fun t => t * 2 ^ 16 + (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8) h24
    calc
      n = (n / 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := h08
      _ = ((n / 2 ^ 8 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        rw [h16']
      _ = ((n / 2 ^ 16) * 2 ^ 8 + (n / 2 ^ 8) % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        simp [hdiv16]
      _ = (n / 2 ^ 16) * 2 ^ 16 + (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        exact congrArg (fun t => t + n % 2 ^ 8)
          (hmul_pow8 (n / 2 ^ 16) (n / 2 ^ 8 % 2 ^ 8))
      _ = ((n / 2 ^ 16 / 2 ^ 8) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        rw [h24']
      _ = ((n / 2 ^ 24) * 2 ^ 8 + (n / 2 ^ 16) % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        simp [hdiv24]
      _ = (n / 2 ^ 24) * 2 ^ 24 +
            (n / 2 ^ 16 % 2 ^ 8) * 2 ^ 16 +
            (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8 := by
        exact congrArg (fun t => t + (n / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 + n % 2 ^ 8)
          (hmul_pow16 (n / 2 ^ 24) (n / 2 ^ 16 % 2 ^ 8))
  have hdecomp' :
      ((n / 2 ^ 24) % 256) * 2 ^ 24 +
        ((n / 2 ^ 16) % 256) * 2 ^ 16 +
        ((n / 2 ^ 8) % 256) * 2 ^ 8 + n % 256 = n := by
    simpa [h256, h24mod] using hdecomp
  simpa [hread] using hdecomp'

/-- Reading a big-endian 32-bit value depends only on the extracted four-byte slice. -/
lemma readU32BE_extract (bytes : ByteArray) (pos : Nat) (h : pos + 3 < bytes.size) :
    readU32BE bytes pos h =
      readU32BE (bytes.extract pos (pos + 4)) 0 (by
        have hle : pos + 4 ≤ bytes.size := Nat.succ_le_of_lt h
        simp [ByteArray.size_extract, Nat.min_eq_left hle, Nat.add_sub_cancel_left]) := by
  cases bytes with
  | mk data =>
      simp [readU32BE, ByteArray.extract, ByteArray.get]
      rfl

/-- `readU32BE` ignores which proof witnesses the same bounds check. -/
lemma readU32BE_proof_irrel {bytes : ByteArray} {pos : Nat}
    (h1 h2 : pos + 3 < bytes.size) :
    readU32BE bytes pos h1 = readU32BE bytes pos h2 := by
  rfl

/-- If a four-byte slice equals `u32be n`, reading it back yields `n`. -/
lemma readU32BE_of_extract_eq (bytes : ByteArray) (pos n : Nat)
    (h : pos + 3 < bytes.size)
    (hextract : bytes.extract pos (pos + 4) = u32be n)
    (hn : n < 2 ^ 32) :
    readU32BE bytes pos h = n := by
  have h' := readU32BE_extract (bytes := bytes) (pos := pos) h
  have hcanon : readU32BE (u32be n) 0 (by simp [u32be_size]) = n :=
    readU32BE_u32be n hn
  have h'' :
      readU32BE (bytes.extract pos (pos + 4)) 0 (by
        have hle : pos + 4 ≤ bytes.size := Nat.succ_le_of_lt h
        simp [ByteArray.size_extract, Nat.min_eq_left hle]) = n := by
    simpa [hextract, readU32BE_proof_irrel] using hcanon
  exact h'.trans h''

end U32Helpers

end Lemmas

end Bitmaps
