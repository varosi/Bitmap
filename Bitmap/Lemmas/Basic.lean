import Bitmap.Basic
import Init.Data.Nat.Lemmas

universe u

namespace Bitmaps

namespace Lemmas

class LawfulAlphaChannel (RangeT : Type u) [AlphaChannel RangeT] : Prop where
  toNat_natCast_of_le_max :
    ∀ n : Nat, n ≤ AlphaChannel.maxValue (RangeT := RangeT) →
      AlphaChannel.toNat (Nat.cast (R := RangeT) n) = n
  natCast_toNat : ∀ x : RangeT,
      (Nat.cast (R := RangeT) (AlphaChannel.toNat x)) = x
  toNat_le_max : ∀ x : RangeT,
      AlphaChannel.toNat x ≤ AlphaChannel.maxValue (RangeT := RangeT)
  maxValue_pos : 0 < AlphaChannel.maxValue (RangeT := RangeT)

instance : LawfulAlphaChannel UInt8 where
  toNat_natCast_of_le_max := by
    intro n hn
    have hn' : n ≤ 255 := by simpa using hn
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

instance : LawfulAlphaChannel UInt16 where
  toNat_natCast_of_le_max := by
    intro n hn
    have hn' : n ≤ 65535 := by simpa using hn
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

lemma alphaDivRound_zero_left (den : Nat) : alphaDivRound 0 den = 0 := by
  cases den with
  | zero => simp [alphaDivRound]
  | succ d =>
      have hlt : Nat.succ d / 2 < Nat.succ d :=
        Nat.div_lt_self (Nat.succ_pos d) (by decide : 1 < (2 : Nat))
      unfold alphaDivRound
      simp [Nat.div_eq_of_lt hlt]

lemma alphaDivRound_mul_right (x den : Nat) (hden : 0 < den) :
    alphaDivRound (x * den) den = x := by
  unfold alphaDivRound
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

lemma alphaClamp_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (n : Nat) :
    AlphaChannel.toNat (alphaClamp (RangeT := RangeT) n) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT)) n := by
  unfold alphaClamp
  exact LawfulAlphaChannel.toNat_natCast_of_le_max
    (RangeT := RangeT)
    (Nat.min (AlphaChannel.maxValue (RangeT := RangeT)) n)
    (Nat.min_le_left _ _)

lemma alphaClamp_toNat_self {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (x : RangeT) :
    alphaClamp (RangeT := RangeT) (AlphaChannel.toNat x) = x := by
  unfold alphaClamp
  have hle : AlphaChannel.toNat x ≤ AlphaChannel.maxValue (RangeT := RangeT) :=
    LawfulAlphaChannel.toNat_le_max (RangeT := RangeT) x
  have hmin : Nat.min (AlphaChannel.maxValue (RangeT := RangeT)) (AlphaChannel.toNat x) =
      AlphaChannel.toNat x := by
    exact Nat.min_eq_right hle
  simpa [hmin] using (LawfulAlphaChannel.natCast_toNat (RangeT := RangeT) x)

lemma alphaOver_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstA : RangeT) :
    alphaOver (RangeT := RangeT) dstA (Nat.cast (R := RangeT) 0) = dstA := by
  unfold alphaOver
  have hsrc0 : AlphaChannel.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  simp [hsrc0, alphaDivRound_mul_right, LawfulAlphaChannel.maxValue_pos]
  exact alphaClamp_toNat_self (RangeT := RangeT) dstA

lemma alphaOver_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (srcA : RangeT) :
    alphaOver (RangeT := RangeT) (Nat.cast (R := RangeT) 0) srcA = srcA := by
  unfold alphaOver
  have hdst0 : AlphaChannel.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  simp [hdst0, alphaDivRound_zero_left]
  exact alphaClamp_toNat_self (RangeT := RangeT) srcA

lemma alphaOver_src_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstA : RangeT) :
    alphaOver (RangeT := RangeT) dstA
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  unfold alphaOver
  have hsrcMax : AlphaChannel.toNat
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) =
      AlphaChannel.maxValue (RangeT := RangeT) := by
    exact LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT)
      (AlphaChannel.maxValue (RangeT := RangeT)) (Nat.le_refl _)
  simp [hsrcMax, alphaDivRound_zero_left]
  unfold alphaClamp
  simp

lemma alphaClamp_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (n : Nat) :
    AlphaChannel.toNat (alphaClamp (RangeT := RangeT) n) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  rw [alphaClamp_toNat_eq_min (RangeT := RangeT) n]
  exact Nat.min_le_left _ _

lemma alphaClamp_idempotent {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (n : Nat) :
    alphaClamp (RangeT := RangeT)
      (AlphaChannel.toNat (alphaClamp (RangeT := RangeT) n)) =
      alphaClamp (RangeT := RangeT) n := by
  exact alphaClamp_toNat_self (RangeT := RangeT) (alphaClamp (RangeT := RangeT) n)

lemma alphaOver_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstA srcA : RangeT) :
    AlphaChannel.toNat (alphaOver (RangeT := RangeT) dstA srcA) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT))
        (AlphaChannel.toNat srcA +
          alphaDivRound
            (AlphaChannel.toNat dstA *
              ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat srcA))
            (AlphaChannel.maxValue (RangeT := RangeT))) := by
  unfold alphaOver
  exact alphaClamp_toNat_eq_min (RangeT := RangeT) _

lemma alphaOver_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstA srcA : RangeT) :
    AlphaChannel.toNat (alphaOver (RangeT := RangeT) dstA srcA) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  rw [alphaOver_toNat_eq_min (RangeT := RangeT) dstA srcA]
  exact Nat.min_le_left _ _

lemma rgbaOver_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).a = alphaOver (RangeT := RangeT) dst.a src.a := by
  rfl

lemma rgbaMultiplyOver_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a =
      alphaOver (RangeT := RangeT) dst.a src.a := by
  unfold rgbaMultiplyOver rgbaOver
  rfl

lemma rgbaOver_alpha_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).a = dst.a := by
  rw [rgbaOver_alpha, hsrc]
  exact alphaOver_src_zero (RangeT := RangeT) dst.a

lemma rgbaOver_alpha_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).a = src.a := by
  rw [rgbaOver_alpha, hdst]
  exact alphaOver_dst_zero (RangeT := RangeT) src.a

lemma rgbaOver_alpha_src_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaOver_alpha, hsrc]
  exact alphaOver_src_full (RangeT := RangeT) dst.a

lemma rgbaOver_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).a) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_alpha] using
    (alphaOver_toNat_le_max (RangeT := RangeT) dst.a src.a)

lemma rgbaOver_alpha_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).a) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT))
        (AlphaChannel.toNat src.a +
          alphaDivRound
            (AlphaChannel.toNat dst.a *
              ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat src.a))
            (AlphaChannel.maxValue (RangeT := RangeT))) := by
  simpa [rgbaOver_alpha] using
    (alphaOver_toNat_eq_min (RangeT := RangeT) dst.a src.a)

lemma rgbaMultiplyOver_alpha_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a = dst.a := by
  rw [rgbaMultiplyOver_alpha, hsrc]
  exact alphaOver_src_zero (RangeT := RangeT) dst.a

lemma rgbaMultiplyOver_alpha_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a = src.a := by
  rw [rgbaMultiplyOver_alpha, hdst]
  exact alphaOver_dst_zero (RangeT := RangeT) src.a

lemma rgbaMultiplyOver_alpha_src_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaMultiplyOver_alpha, hsrc]
  exact alphaOver_src_full (RangeT := RangeT) dst.a

lemma rgbaMultiplyOver_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).a) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_alpha] using
    (alphaOver_toNat_le_max (RangeT := RangeT) dst.a src.a)

lemma alphaOver_dst_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (srcA : RangeT) :
    alphaOver (RangeT := RangeT)
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) srcA =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  have hdstMax : AlphaChannel.toNat
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) =
      AlphaChannel.maxValue (RangeT := RangeT) := by
    exact LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT)
      (AlphaChannel.maxValue (RangeT := RangeT)) (Nat.le_refl _)
  have hmaxPos : 0 < AlphaChannel.maxValue (RangeT := RangeT) :=
    LawfulAlphaChannel.maxValue_pos (RangeT := RangeT)
  have hdiv :
      alphaDivRound
        ((AlphaChannel.maxValue (RangeT := RangeT)) *
          ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat srcA))
        (AlphaChannel.maxValue (RangeT := RangeT)) =
      (AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat srcA := by
    simpa [Nat.mul_comm] using
      (alphaDivRound_mul_right
        ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat srcA)
        (AlphaChannel.maxValue (RangeT := RangeT)) hmaxPos)
  have hle : AlphaChannel.toNat srcA ≤ AlphaChannel.maxValue (RangeT := RangeT) :=
    LawfulAlphaChannel.toNat_le_max (RangeT := RangeT) srcA
  have hs : AlphaChannel.toNat srcA +
      ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat srcA) =
      AlphaChannel.maxValue (RangeT := RangeT) := by
    exact Nat.add_sub_of_le hle
  have hcast : alphaClamp (RangeT := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
    unfold alphaClamp
    simp
  simpa [alphaOver, hdstMax, hdiv, hs] using hcast

lemma alphaOver_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] :
    alphaOver (RangeT := RangeT) (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) =
      (Nat.cast (R := RangeT) 0) := by
  have h := alphaOver_dst_zero (RangeT := RangeT) (srcA := (Nat.cast (R := RangeT) 0))
  simpa using h

lemma rgbaOver_alpha_dst_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaOver_alpha, hdst]
  exact alphaOver_dst_full (RangeT := RangeT) src.a

lemma rgbaMultiplyOver_alpha_dst_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaMultiplyOver_alpha, hdst]
  exact alphaOver_dst_full (RangeT := RangeT) src.a

lemma rgbaOver_alpha_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).a = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_alpha, hdst, hsrc]
  exact alphaOver_zero_zero (RangeT := RangeT)

lemma rgbaMultiplyOver_alpha_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_alpha, hdst, hsrc]
  exact alphaOver_zero_zero (RangeT := RangeT)

lemma rgbaOver_r {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).r =
      blendChannelOver (RangeT := RangeT) dst.r src.r dst.a src.a := by
  rfl

lemma rgbaOver_g {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).g =
      blendChannelOver (RangeT := RangeT) dst.g src.g dst.a src.a := by
  rfl

lemma rgbaOver_b {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).b =
      blendChannelOver (RangeT := RangeT) dst.b src.b dst.a src.a := by
  rfl

lemma rgbaMultiplyOver_r {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).r =
      blendChannelOver (RangeT := RangeT)
        dst.r (alphaMulNorm (RangeT := RangeT) dst.r src.r) dst.a src.a := by
  simp [rgbaMultiplyOver, rgbaOver]

lemma rgbaMultiplyOver_g {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).g =
      blendChannelOver (RangeT := RangeT)
        dst.g (alphaMulNorm (RangeT := RangeT) dst.g src.g) dst.a src.a := by
  simp [rgbaMultiplyOver, rgbaOver]

lemma rgbaMultiplyOver_b {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).b =
      blendChannelOver (RangeT := RangeT)
        dst.b (alphaMulNorm (RangeT := RangeT) dst.b src.b) dst.a src.a := by
  simp [rgbaMultiplyOver, rgbaOver]

lemma pixelRGBA_add_eq_rgbaOver {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    dst + src = rgbaOver (RangeT := RangeT) dst src := rfl

lemma pixelRGBA_mul_eq_rgbaMultiplyOver {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    dst * src = rgbaMultiplyOver (RangeT := RangeT) dst src := rfl

lemma pixelRGBA_add_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst + src).a = alphaOver (RangeT := RangeT) dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_alpha (RangeT := RangeT) dst src)

lemma pixelRGBA_mul_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst * src).a = alphaOver (RangeT := RangeT) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_alpha (RangeT := RangeT) dst src)

lemma pixelRGBA_add_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst + src).a) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

lemma pixelRGBA_mul_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst * src).a) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

end Lemmas

end Bitmaps
