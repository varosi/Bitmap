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

/-- `alphaDivRound` returns `0` when its numerator is `0`. -/
lemma alphaDivRound_zero_left (den : Nat) : alphaDivRound 0 den = 0 := by
  cases den with
  | zero => simp [alphaDivRound]
  | succ d =>
      have hlt : Nat.succ d / 2 < Nat.succ d :=
        Nat.div_lt_self (Nat.succ_pos d) (by decide : 1 < (2 : Nat))
      unfold alphaDivRound
      simp [Nat.div_eq_of_lt hlt]

/-- `alphaDivRound (x * den) den = x` for positive `den`. -/
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

/-- `alphaClamp` converts back to `Nat` as `min maxValue n`. -/
lemma alphaClamp_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (n : Nat) :
    AlphaChannel.toNat (alphaClamp (RangeT := RangeT) n) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT)) n := by
  unfold alphaClamp
  exact LawfulAlphaChannel.toNat_natCast_of_le_max
    (RangeT := RangeT)
    (Nat.min (AlphaChannel.maxValue (RangeT := RangeT)) n)
    (Nat.min_le_left _ _)

/-- `alphaClamp` is a left inverse of `toNat` on channel values. -/
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

/-- `alphaOver dst 0 = dst`. -/
lemma alphaOver_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstA : RangeT) :
    alphaOver (RangeT := RangeT) dstA (Nat.cast (R := RangeT) 0) = dstA := by
  unfold alphaOver
  have hsrc0 : AlphaChannel.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  simp [hsrc0, alphaDivRound_mul_right, LawfulAlphaChannel.maxValue_pos]
  exact alphaClamp_toNat_self (RangeT := RangeT) dstA

/-- `alphaOver 0 src = src`. -/
lemma alphaOver_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (srcA : RangeT) :
    alphaOver (RangeT := RangeT) (Nat.cast (R := RangeT) 0) srcA = srcA := by
  unfold alphaOver
  have hdst0 : AlphaChannel.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  simp [hdst0, alphaDivRound_zero_left]
  exact alphaClamp_toNat_self (RangeT := RangeT) srcA

/-- `alphaOver dst max = max`. -/
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

/-- The `Nat` value of `alphaClamp n` is bounded by `maxValue`. -/
lemma alphaClamp_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (n : Nat) :
    AlphaChannel.toNat (alphaClamp (RangeT := RangeT) n) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  rw [alphaClamp_toNat_eq_min (RangeT := RangeT) n]
  exact Nat.min_le_left _ _

/-- `alphaClamp` is idempotent after converting through `toNat`. -/
lemma alphaClamp_idempotent {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (n : Nat) :
    alphaClamp (RangeT := RangeT)
      (AlphaChannel.toNat (alphaClamp (RangeT := RangeT) n)) =
      alphaClamp (RangeT := RangeT) n := by
  exact alphaClamp_toNat_self (RangeT := RangeT) (alphaClamp (RangeT := RangeT) n)

/-- `alphaMulNorm` is commutative. -/
lemma alphaMulNorm_comm {RangeT : Type u} [AlphaChannel RangeT]
    (x y : RangeT) :
    alphaMulNorm (RangeT := RangeT) x y = alphaMulNorm (RangeT := RangeT) y x := by
  unfold alphaMulNorm
  simp [Nat.mul_comm]

/-- Characterizes `toNat (alphaMulNorm x y)` as a clamped rounded product. -/
lemma alphaMulNorm_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (x y : RangeT) :
    AlphaChannel.toNat (alphaMulNorm (RangeT := RangeT) x y) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT))
        (alphaDivRound (AlphaChannel.toNat x * AlphaChannel.toNat y)
          (AlphaChannel.maxValue (RangeT := RangeT))) := by
  unfold alphaMulNorm
  exact alphaClamp_toNat_eq_min (RangeT := RangeT) _

/-- The `Nat` value of `alphaMulNorm x y` is bounded by `maxValue`. -/
lemma alphaMulNorm_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (x y : RangeT) :
    AlphaChannel.toNat (alphaMulNorm (RangeT := RangeT) x y) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  rw [alphaMulNorm_toNat_eq_min (RangeT := RangeT) x y]
  exact Nat.min_le_left _ _

/-- `alphaMulNorm 0 y = 0`. -/
lemma alphaMulNorm_zero_left {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (y : RangeT) :
    alphaMulNorm (RangeT := RangeT) (Nat.cast (R := RangeT) 0) y =
      Nat.cast (R := RangeT) 0 := by
  have h0 : AlphaChannel.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  unfold alphaMulNorm
  unfold alphaClamp
  simp [h0, alphaDivRound_zero_left]

/-- `alphaMulNorm x 0 = 0`. -/
lemma alphaMulNorm_zero_right {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (x : RangeT) :
    alphaMulNorm (RangeT := RangeT) x (Nat.cast (R := RangeT) 0) =
      Nat.cast (R := RangeT) 0 := by
  rw [alphaMulNorm_comm]
  exact alphaMulNorm_zero_left (RangeT := RangeT) x

/-- `alphaMulNorm max y = y`. -/
lemma alphaMulNorm_full_left {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (y : RangeT) :
    alphaMulNorm (RangeT := RangeT)
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) y = y := by
  have htoNatMax : AlphaChannel.toNat
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) =
      AlphaChannel.maxValue (RangeT := RangeT) := by
    exact LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT)
      (AlphaChannel.maxValue (RangeT := RangeT)) (Nat.le_refl _)
  have hmaxPos : 0 < AlphaChannel.maxValue (RangeT := RangeT) :=
    LawfulAlphaChannel.maxValue_pos (RangeT := RangeT)
  have hdiv :
      alphaDivRound
        ((AlphaChannel.maxValue (RangeT := RangeT)) * AlphaChannel.toNat y)
        (AlphaChannel.maxValue (RangeT := RangeT)) =
      AlphaChannel.toNat y := by
    simpa [Nat.mul_comm] using
      (alphaDivRound_mul_right (AlphaChannel.toNat y)
        (AlphaChannel.maxValue (RangeT := RangeT)) hmaxPos)
  unfold alphaMulNorm
  rw [htoNatMax]
  simpa [hdiv] using (alphaClamp_toNat_self (RangeT := RangeT) y)

/-- `alphaMulNorm x max = x`. -/
lemma alphaMulNorm_full_right {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (x : RangeT) :
    alphaMulNorm (RangeT := RangeT) x
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) = x := by
  rw [alphaMulNorm_comm]
  exact alphaMulNorm_full_left (RangeT := RangeT) x

/-- `alphaMulNorm 0 0 = 0`. -/
lemma alphaMulNorm_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] :
    alphaMulNorm (RangeT := RangeT) (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) =
      Nat.cast (R := RangeT) 0 := by
  exact alphaMulNorm_zero_left (RangeT := RangeT) (Nat.cast (R := RangeT) 0)

/-- `alphaMulNorm max max = max`. -/
lemma alphaMulNorm_full_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] :
    alphaMulNorm (RangeT := RangeT)
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)))
      (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  exact alphaMulNorm_full_left (RangeT := RangeT)
    (Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)))

/-- Characterizes `toNat (alphaOver dst src)` as a clamped over-alpha formula. -/
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

/-- The `Nat` value of `alphaOver dst src` is bounded by `maxValue`. -/
lemma alphaOver_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstA srcA : RangeT) :
    AlphaChannel.toNat (alphaOver (RangeT := RangeT) dstA srcA) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  rw [alphaOver_toNat_eq_min (RangeT := RangeT) dstA srcA]
  exact Nat.min_le_left _ _

/-- The blended channel value is always bounded by `maxValue` in `Nat` form. -/
lemma blendChannelOver_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstC srcC dstA srcA : RangeT) :
    AlphaChannel.toNat (blendChannelOver (RangeT := RangeT) dstC srcC dstA srcA) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  unfold blendChannelOver
  dsimp
  split
  · simpa using (alphaClamp_toNat_le_max (RangeT := RangeT) 0)
  · simpa using
      (alphaClamp_toNat_le_max (RangeT := RangeT)
        (alphaDivRound
          ((AlphaChannel.toNat srcC * AlphaChannel.toNat srcA +
              alphaDivRound
                (AlphaChannel.toNat dstC * AlphaChannel.toNat dstA *
                  (AlphaChannel.maxValue (RangeT := RangeT) - AlphaChannel.toNat srcA))
                (AlphaChannel.maxValue (RangeT := RangeT))) *
            AlphaChannel.maxValue (RangeT := RangeT))
          (AlphaChannel.toNat srcA +
            alphaDivRound
              (AlphaChannel.toNat dstA *
                (AlphaChannel.maxValue (RangeT := RangeT) - AlphaChannel.toNat srcA))
              (AlphaChannel.maxValue (RangeT := RangeT))))
      )

/-- With both alphas `0`, `blendChannelOver` returns channel `0`. -/
lemma blendChannelOver_alpha_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstC srcC : RangeT) :
    blendChannelOver (RangeT := RangeT) dstC srcC
      (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) =
      Nat.cast (R := RangeT) 0 := by
  have htoNat0 : AlphaChannel.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  have hdiv0 :
      alphaDivRound 0 (AlphaChannel.maxValue (RangeT := RangeT)) = 0 := by
    simpa using (alphaDivRound_zero_left (AlphaChannel.maxValue (RangeT := RangeT)))
  unfold blendChannelOver
  unfold alphaClamp
  simp [htoNat0, hdiv0]

/-- With both input channel values `0`, `blendChannelOver` returns `0`. -/
lemma blendChannelOver_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dstA srcA : RangeT) :
    blendChannelOver (RangeT := RangeT)
      (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) dstA srcA =
      Nat.cast (R := RangeT) 0 := by
  have htoNat0 : AlphaChannel.toNat (Nat.cast (R := RangeT) 0) = 0 := by
    simpa using (LawfulAlphaChannel.toNat_natCast_of_le_max (RangeT := RangeT) 0 (Nat.zero_le _))
  unfold blendChannelOver
  unfold alphaClamp
  simp [htoNat0, alphaDivRound_zero_left]

/-- `rgbaOver` computes alpha as `alphaOver dst.a src.a`. -/
lemma rgbaOver_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).a = alphaOver (RangeT := RangeT) dst.a src.a := by
  rfl

/-- `rgbaMultiplyOver` computes alpha as `alphaOver dst.a src.a`. -/
lemma rgbaMultiplyOver_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a =
      alphaOver (RangeT := RangeT) dst.a src.a := by
  unfold rgbaMultiplyOver rgbaOver
  rfl

/-- For `rgbaOver`, source alpha is `0`, so output alpha is destination alpha. -/
lemma rgbaOver_alpha_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).a = dst.a := by
  rw [rgbaOver_alpha, hsrc]
  exact alphaOver_src_zero (RangeT := RangeT) dst.a

/-- For `rgbaOver`, destination alpha is `0`, so output alpha is source alpha. -/
lemma rgbaOver_alpha_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).a = src.a := by
  rw [rgbaOver_alpha, hdst]
  exact alphaOver_dst_zero (RangeT := RangeT) src.a

/-- For `rgbaOver`, source alpha is maximal, so output alpha is maximal. -/
lemma rgbaOver_alpha_src_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaOver_alpha, hsrc]
  exact alphaOver_src_full (RangeT := RangeT) dst.a

/-- `toNat` of `rgbaOver` alpha is bounded by `maxValue`. -/
lemma rgbaOver_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).a) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_alpha] using
    (alphaOver_toNat_le_max (RangeT := RangeT) dst.a src.a)

/-- Characterizes `toNat` of `rgbaOver` alpha with the clamped over-alpha formula. -/
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

/-- For `rgbaMultiplyOver`, source alpha is `0`, so output alpha is destination alpha. -/
lemma rgbaMultiplyOver_alpha_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a = dst.a := by
  rw [rgbaMultiplyOver_alpha, hsrc]
  exact alphaOver_src_zero (RangeT := RangeT) dst.a

/-- For `rgbaMultiplyOver`, destination alpha is `0`, so output alpha is source alpha. -/
lemma rgbaMultiplyOver_alpha_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a = src.a := by
  rw [rgbaMultiplyOver_alpha, hdst]
  exact alphaOver_dst_zero (RangeT := RangeT) src.a

/-- For `rgbaMultiplyOver`, source alpha is maximal, so output alpha is maximal. -/
lemma rgbaMultiplyOver_alpha_src_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaMultiplyOver_alpha, hsrc]
  exact alphaOver_src_full (RangeT := RangeT) dst.a

/-- `toNat` of `rgbaMultiplyOver` alpha is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).a) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_alpha] using
    (alphaOver_toNat_le_max (RangeT := RangeT) dst.a src.a)

/-- Characterizes `toNat` of `rgbaMultiplyOver` alpha with the clamped over-alpha formula. -/
lemma rgbaMultiplyOver_alpha_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).a) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT))
        (AlphaChannel.toNat src.a +
          alphaDivRound
            (AlphaChannel.toNat dst.a *
              ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat src.a))
            (AlphaChannel.maxValue (RangeT := RangeT))) := by
  simpa [rgbaMultiplyOver_alpha] using
    (alphaOver_toNat_eq_min (RangeT := RangeT) dst.a src.a)

/-- `alphaOver max src = max`. -/
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

/-- `alphaOver 0 0 = 0`. -/
lemma alphaOver_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] :
    alphaOver (RangeT := RangeT) (Nat.cast (R := RangeT) 0) (Nat.cast (R := RangeT) 0) =
      (Nat.cast (R := RangeT) 0) := by
  have h := alphaOver_dst_zero (RangeT := RangeT) (srcA := (Nat.cast (R := RangeT) 0))
  simpa using h

/-- For `rgbaOver`, destination alpha is maximal, so output alpha is maximal. -/
lemma rgbaOver_alpha_dst_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaOver_alpha, hdst]
  exact alphaOver_dst_full (RangeT := RangeT) src.a

/-- For `rgbaMultiplyOver`, destination alpha is maximal, so output alpha is maximal. -/
lemma rgbaMultiplyOver_alpha_dst_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a =
      Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  rw [rgbaMultiplyOver_alpha, hdst]
  exact alphaOver_dst_full (RangeT := RangeT) src.a

/-- For `rgbaOver`, both input alphas are `0`, so output alpha is `0`. -/
lemma rgbaOver_alpha_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).a = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_alpha, hdst, hsrc]
  exact alphaOver_zero_zero (RangeT := RangeT)

/-- For `rgbaMultiplyOver`, both input alphas are `0`, so output alpha is `0`. -/
lemma rgbaMultiplyOver_alpha_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).a = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_alpha, hdst, hsrc]
  exact alphaOver_zero_zero (RangeT := RangeT)

/-- Projects the red channel of `rgbaOver` to the corresponding `blendChannelOver` expression. -/
lemma rgbaOver_r {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).r =
      blendChannelOver (RangeT := RangeT) dst.r src.r dst.a src.a := by
  rfl

/-- Projects the green channel of `rgbaOver` to the corresponding `blendChannelOver` expression. -/
lemma rgbaOver_g {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).g =
      blendChannelOver (RangeT := RangeT) dst.g src.g dst.a src.a := by
  rfl

/-- Projects the blue channel of `rgbaOver` to the corresponding `blendChannelOver` expression. -/
lemma rgbaOver_b {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaOver (RangeT := RangeT) dst src).b =
      blendChannelOver (RangeT := RangeT) dst.b src.b dst.a src.a := by
  rfl

/-- `toNat` of the red channel of `rgbaOver` is bounded by `maxValue`. -/
lemma rgbaOver_toNat_r_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).r) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_r] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT) dst.r src.r dst.a src.a)

/-- `toNat` of the green channel of `rgbaOver` is bounded by `maxValue`. -/
lemma rgbaOver_toNat_g_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).g) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_g] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT) dst.g src.g dst.a src.a)

/-- `toNat` of the blue channel of `rgbaOver` is bounded by `maxValue`. -/
lemma rgbaOver_toNat_b_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).b) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaOver_b] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT) dst.b src.b dst.a src.a)

/-- All channel values of `rgbaOver` are bounded by `maxValue` after `toNat`. -/
lemma rgbaOver_channels_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).r) ≤
        AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).g) ≤
        AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).b) ≤
        AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((rgbaOver (RangeT := RangeT) dst src).a) ≤
        AlphaChannel.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact rgbaOver_toNat_r_le_max (RangeT := RangeT) dst src
  · exact rgbaOver_toNat_g_le_max (RangeT := RangeT) dst src
  · exact rgbaOver_toNat_b_le_max (RangeT := RangeT) dst src
  · exact rgbaOver_alpha_toNat_le_max (RangeT := RangeT) dst src

/-- For `rgbaOver`, if both input alphas are `0`, the red channel is `0`. -/
lemma rgbaOver_r_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_r]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT) dst.r src.r)

/-- For `rgbaOver`, if both input alphas are `0`, the green channel is `0`. -/
lemma rgbaOver_g_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_g]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT) dst.g src.g)

/-- For `rgbaOver`, if both input alphas are `0`, the blue channel is `0`. -/
lemma rgbaOver_b_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_b]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT) dst.b src.b)

/-- For `rgbaOver`, if both input red channels are `0`, the output red channel is `0`. -/
lemma rgbaOver_r_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_r, hdst, hsrc]
  exact blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a

/-- For `rgbaOver`, if both input green channels are `0`, the output green channel is `0`. -/
lemma rgbaOver_g_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_g, hdst, hsrc]
  exact blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a

/-- For `rgbaOver`, if both input blue channels are `0`, the output blue channel is `0`. -/
lemma rgbaOver_b_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaOver_b, hdst, hsrc]
  exact blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a

/-- For `rgbaOver`, if both input RGB channels are all `0`, output RGB channels are all `0`. -/
lemma rgbaOver_rgb_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    (rgbaOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 ∧
    (rgbaOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 ∧
    (rgbaOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact rgbaOver_r_channel_zero_zero (RangeT := RangeT) dst src hdstR hsrcR
  · exact rgbaOver_g_channel_zero_zero (RangeT := RangeT) dst src hdstG hsrcG
  · exact rgbaOver_b_channel_zero_zero (RangeT := RangeT) dst src hdstB hsrcB

/-- Projects the red channel of `rgbaMultiplyOver` to the corresponding `blendChannelOver` expression. -/
lemma rgbaMultiplyOver_r {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).r =
      blendChannelOver (RangeT := RangeT)
        dst.r (alphaMulNorm (RangeT := RangeT) dst.r src.r) dst.a src.a := by
  simp [rgbaMultiplyOver, rgbaOver]

/-- Projects the green channel of `rgbaMultiplyOver` to the corresponding `blendChannelOver` expression. -/
lemma rgbaMultiplyOver_g {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).g =
      blendChannelOver (RangeT := RangeT)
        dst.g (alphaMulNorm (RangeT := RangeT) dst.g src.g) dst.a src.a := by
  simp [rgbaMultiplyOver, rgbaOver]

/-- Projects the blue channel of `rgbaMultiplyOver` to the corresponding `blendChannelOver` expression. -/
lemma rgbaMultiplyOver_b {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).b =
      blendChannelOver (RangeT := RangeT)
        dst.b (alphaMulNorm (RangeT := RangeT) dst.b src.b) dst.a src.a := by
  simp [rgbaMultiplyOver, rgbaOver]

/-- `toNat` of the red channel of `rgbaMultiplyOver` is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_toNat_r_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).r) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_r] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT)
      dst.r (alphaMulNorm (RangeT := RangeT) dst.r src.r) dst.a src.a)

/-- `toNat` of the green channel of `rgbaMultiplyOver` is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_toNat_g_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).g) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_g] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT)
      dst.g (alphaMulNorm (RangeT := RangeT) dst.g src.g) dst.a src.a)

/-- `toNat` of the blue channel of `rgbaMultiplyOver` is bounded by `maxValue`. -/
lemma rgbaMultiplyOver_toNat_b_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).b) ≤
      AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [rgbaMultiplyOver_b] using
    (blendChannelOver_toNat_le_max (RangeT := RangeT)
      dst.b (alphaMulNorm (RangeT := RangeT) dst.b src.b) dst.a src.a)

/-- All channel values of `rgbaMultiplyOver` are bounded by `maxValue` after `toNat`. -/
lemma rgbaMultiplyOver_channels_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).r) ≤
        AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).g) ≤
        AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).b) ≤
        AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((rgbaMultiplyOver (RangeT := RangeT) dst src).a) ≤
        AlphaChannel.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact rgbaMultiplyOver_toNat_r_le_max (RangeT := RangeT) dst src
  · exact rgbaMultiplyOver_toNat_g_le_max (RangeT := RangeT) dst src
  · exact rgbaMultiplyOver_toNat_b_le_max (RangeT := RangeT) dst src
  · exact rgbaMultiplyOver_alpha_toNat_le_max (RangeT := RangeT) dst src

/-- For `rgbaMultiplyOver`, if both input alphas are `0`, the red channel is `0`. -/
lemma rgbaMultiplyOver_r_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_r]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT)
      dst.r (alphaMulNorm (RangeT := RangeT) dst.r src.r))

/-- For `rgbaMultiplyOver`, if both input alphas are `0`, the green channel is `0`. -/
lemma rgbaMultiplyOver_g_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_g]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT)
      dst.g (alphaMulNorm (RangeT := RangeT) dst.g src.g))

/-- For `rgbaMultiplyOver`, if both input alphas are `0`, the blue channel is `0`. -/
lemma rgbaMultiplyOver_b_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_b]
  simpa [hdst, hsrc] using
    (blendChannelOver_alpha_zero_zero (RangeT := RangeT)
      dst.b (alphaMulNorm (RangeT := RangeT) dst.b src.b))

/-- For `rgbaMultiplyOver`, if both input red channels are `0`, the output red channel is `0`. -/
lemma rgbaMultiplyOver_r_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_r, hdst, hsrc]
  simpa [alphaMulNorm_zero_zero (RangeT := RangeT)] using
    (blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a)

/-- For `rgbaMultiplyOver`, if both input green channels are `0`, the output green channel is `0`. -/
lemma rgbaMultiplyOver_g_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_g, hdst, hsrc]
  simpa [alphaMulNorm_zero_zero (RangeT := RangeT)] using
    (blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a)

/-- For `rgbaMultiplyOver`, if both input blue channels are `0`, the output blue channel is `0`. -/
lemma rgbaMultiplyOver_b_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  rw [rgbaMultiplyOver_b, hdst, hsrc]
  simpa [alphaMulNorm_zero_zero (RangeT := RangeT)] using
    (blendChannelOver_channel_zero_zero (RangeT := RangeT) dst.a src.a)

/-- For `rgbaMultiplyOver`, if both input RGB channels are all `0`, output RGB channels are all `0`. -/
lemma rgbaMultiplyOver_rgb_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    (rgbaMultiplyOver (RangeT := RangeT) dst src).r = Nat.cast (R := RangeT) 0 ∧
    (rgbaMultiplyOver (RangeT := RangeT) dst src).g = Nat.cast (R := RangeT) 0 ∧
    (rgbaMultiplyOver (RangeT := RangeT) dst src).b = Nat.cast (R := RangeT) 0 := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact rgbaMultiplyOver_r_channel_zero_zero (RangeT := RangeT) dst src hdstR hsrcR
  · exact rgbaMultiplyOver_g_channel_zero_zero (RangeT := RangeT) dst src hdstG hsrcG
  · exact rgbaMultiplyOver_b_channel_zero_zero (RangeT := RangeT) dst src hdstB hsrcB

/-- For `rgbaOver`, if both input alphas are `0`, output is fully transparent black. -/
lemma rgbaOver_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    rgbaOver (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : PixelRGBA RangeT) := by
  cases dst with
  | mk dr dg db da =>
    cases src with
    | mk sr sg sb sa =>
      simp at hdst hsrc
      subst da
      subst sa
      unfold rgbaOver
      simp [blendChannelOver_alpha_zero_zero, alphaOver_zero_zero]

/-- For `rgbaMultiplyOver`, if both input alphas are `0`, output is fully transparent black. -/
lemma rgbaMultiplyOver_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    rgbaMultiplyOver (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : PixelRGBA RangeT) := by
  cases dst with
  | mk dr dg db da =>
    cases src with
    | mk sr sg sb sa =>
      simp at hdst hsrc
      subst da
      subst sa
      unfold rgbaMultiplyOver rgbaOver
      simp [blendChannelOver_alpha_zero_zero, alphaOver_zero_zero]

/-- For `rgbaOver`, if both input RGB channels are black, output RGB stays black and alpha is `alphaOver dst.a src.a`. -/
lemma rgbaOver_black_channels {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    rgbaOver (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := alphaOver (RangeT := RangeT) dst.a src.a } : PixelRGBA RangeT) := by
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
      unfold rgbaOver
      simp [blendChannelOver_channel_zero_zero]

/-- For `rgbaMultiplyOver`, if both input RGB channels are black, output RGB stays black and alpha is `alphaOver dst.a src.a`. -/
lemma rgbaMultiplyOver_black_channels {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdstR : dst.r = Nat.cast (R := RangeT) 0)
    (hsrcR : src.r = Nat.cast (R := RangeT) 0)
    (hdstG : dst.g = Nat.cast (R := RangeT) 0)
    (hsrcG : src.g = Nat.cast (R := RangeT) 0)
    (hdstB : dst.b = Nat.cast (R := RangeT) 0)
    (hsrcB : src.b = Nat.cast (R := RangeT) 0) :
    rgbaMultiplyOver (RangeT := RangeT) dst src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := alphaOver (RangeT := RangeT) dst.a src.a } : PixelRGBA RangeT) := by
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
      unfold rgbaMultiplyOver rgbaOver
      simp [alphaMulNorm_zero_zero, blendChannelOver_channel_zero_zero]

/-- Bridges `dst + src` to `rgbaOver`. -/
lemma pixelRGBA_add_eq_rgbaOver {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    dst + src = rgbaOver (RangeT := RangeT) dst src := rfl

/-- Bridges `dst * src` to `rgbaMultiplyOver`. -/
lemma pixelRGBA_mul_eq_rgbaMultiplyOver {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    dst * src = rgbaMultiplyOver (RangeT := RangeT) dst src := rfl

/-- Alpha channel projection for `dst + src`. -/
lemma pixelRGBA_add_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst + src).a = alphaOver (RangeT := RangeT) dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_alpha (RangeT := RangeT) dst src)

/-- Alpha channel projection for `dst * src`. -/
lemma pixelRGBA_mul_alpha {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst * src).a = alphaOver (RangeT := RangeT) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_alpha (RangeT := RangeT) dst src)

/-- `dst + src` channel projection for the red channel. -/
lemma pixelRGBA_add_r {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst + src).r = blendChannelOver (RangeT := RangeT) dst.r src.r dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_r (RangeT := RangeT) dst src)

/-- `dst + src` channel projection for the green channel. -/
lemma pixelRGBA_add_g {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst + src).g = blendChannelOver (RangeT := RangeT) dst.g src.g dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_g (RangeT := RangeT) dst src)

/-- `dst + src` channel projection for the blue channel. -/
lemma pixelRGBA_add_b {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst + src).b = blendChannelOver (RangeT := RangeT) dst.b src.b dst.a src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using (rgbaOver_b (RangeT := RangeT) dst src)

/-- `dst * src` channel projection for the red channel. -/
lemma pixelRGBA_mul_r {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst * src).r =
      blendChannelOver (RangeT := RangeT)
        dst.r (alphaMulNorm (RangeT := RangeT) dst.r src.r) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_r (RangeT := RangeT) dst src)

/-- `dst * src` channel projection for the green channel. -/
lemma pixelRGBA_mul_g {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst * src).g =
      blendChannelOver (RangeT := RangeT)
        dst.g (alphaMulNorm (RangeT := RangeT) dst.g src.g) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_g (RangeT := RangeT) dst src)

/-- `dst * src` channel projection for the blue channel. -/
lemma pixelRGBA_mul_b {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) :
    (dst * src).b =
      blendChannelOver (RangeT := RangeT)
        dst.b (alphaMulNorm (RangeT := RangeT) dst.b src.b) dst.a src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using (rgbaMultiplyOver_b (RangeT := RangeT) dst src)

/-- `toNat` of the red channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_toNat_r_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst + src).r) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_toNat_r_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the green channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_toNat_g_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst + src).g) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_toNat_g_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the blue channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_toNat_b_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst + src).b) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_toNat_b_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the red channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_toNat_r_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst * src).r) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_toNat_r_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the green channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_toNat_g_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst * src).g) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_toNat_g_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the blue channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_toNat_b_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst * src).b) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_toNat_b_le_max (RangeT := RangeT) dst src)

/-- All channel values of `dst + src` are bounded by `maxValue` after `toNat`. -/
lemma pixelRGBA_add_channels_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst + src).r) ≤ AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((dst + src).g) ≤ AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((dst + src).b) ≤ AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((dst + src).a) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact pixelRGBA_add_toNat_r_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_add_toNat_g_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_add_toNat_b_le_max (RangeT := RangeT) dst src
  · simpa [pixelRGBA_add_eq_rgbaOver] using
      (rgbaOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- All channel values of `dst * src` are bounded by `maxValue` after `toNat`. -/
lemma pixelRGBA_mul_channels_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst * src).r) ≤ AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((dst * src).g) ≤ AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((dst * src).b) ≤ AlphaChannel.maxValue (RangeT := RangeT) ∧
    AlphaChannel.toNat ((dst * src).a) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact pixelRGBA_mul_toNat_r_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_mul_toNat_g_le_max (RangeT := RangeT) dst src
  · exact pixelRGBA_mul_toNat_b_le_max (RangeT := RangeT) dst src
  · simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
      (rgbaMultiplyOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- If both input alphas are `0`, the red channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_r_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_r_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the green channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_g_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_g_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the blue channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_b_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_b_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the red channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_r_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_r_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the green channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_g_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_g_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, the blue channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_b_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_b_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input red channels are `0`, the output red channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_r_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (dst + src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_r_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input green channels are `0`, the output green channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_g_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (dst + src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_g_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input blue channels are `0`, the output blue channel of `dst + src` is `0`. -/
lemma pixelRGBA_add_b_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (dst + src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_b_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input red channels are `0`, the output red channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_r_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.r = Nat.cast (R := RangeT) 0)
    (hsrc : src.r = Nat.cast (R := RangeT) 0) :
    (dst * src).r = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_r_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input green channels are `0`, the output green channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_g_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.g = Nat.cast (R := RangeT) 0)
    (hsrc : src.g = Nat.cast (R := RangeT) 0) :
    (dst * src).g = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_g_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input blue channels are `0`, the output blue channel of `dst * src` is `0`. -/
lemma pixelRGBA_mul_b_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.b = Nat.cast (R := RangeT) 0)
    (hsrc : src.b = Nat.cast (R := RangeT) 0) :
    (dst * src).b = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_b_channel_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input RGB channels are all `0`, the RGB channels of `dst + src` are all `0`. -/
lemma pixelRGBA_add_rgb_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
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
lemma pixelRGBA_mul_rgb_channel_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
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
lemma pixelRGBA_add_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    dst + src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : PixelRGBA RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input alphas are `0`, `dst * src` yields fully transparent black. -/
lemma pixelRGBA_mul_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    dst * src =
      ({ r := Nat.cast (R := RangeT) 0
       , g := Nat.cast (R := RangeT) 0
       , b := Nat.cast (R := RangeT) 0
       , a := Nat.cast (R := RangeT) 0 } : PixelRGBA RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- If both input RGB channels are black, `dst + src` keeps RGB black and computes alpha with `alphaOver`. -/
lemma pixelRGBA_add_black_channels {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
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
       , a := alphaOver (RangeT := RangeT) dst.a src.a } : PixelRGBA RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_black_channels (RangeT := RangeT) dst src
      hdstR hsrcR hdstG hsrcG hdstB hsrcB)

/-- If both input RGB channels are black, `dst * src` keeps RGB black and computes alpha with `alphaOver`. -/
lemma pixelRGBA_mul_black_channels {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
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
       , a := alphaOver (RangeT := RangeT) dst.a src.a } : PixelRGBA RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_black_channels (RangeT := RangeT) dst src
      hdstR hsrcR hdstG hsrcG hdstB hsrcB)

/-- `toNat` of the alpha channel of `dst + src` is bounded by `maxValue`. -/
lemma pixelRGBA_add_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst + src).a) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- `toNat` of the alpha channel of `dst * src` is bounded by `maxValue`. -/
lemma pixelRGBA_mul_alpha_toNat_le_max {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst * src).a) ≤ AlphaChannel.maxValue (RangeT := RangeT) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_toNat_le_max (RangeT := RangeT) dst src)

/-- Characterizes `toNat` of the alpha channel of `dst + src` with the clamped over-alpha formula. -/
lemma pixelRGBA_add_alpha_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst + src).a) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT))
        (AlphaChannel.toNat src.a +
          alphaDivRound
            (AlphaChannel.toNat dst.a *
              ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat src.a))
            (AlphaChannel.maxValue (RangeT := RangeT))) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_toNat_eq_min (RangeT := RangeT) dst src)

/-- Characterizes `toNat` of the alpha channel of `dst * src` with the clamped over-alpha formula. -/
lemma pixelRGBA_mul_alpha_toNat_eq_min {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT) :
    AlphaChannel.toNat ((dst * src).a) =
      Nat.min (AlphaChannel.maxValue (RangeT := RangeT))
        (AlphaChannel.toNat src.a +
          alphaDivRound
            (AlphaChannel.toNat dst.a *
              ((AlphaChannel.maxValue (RangeT := RangeT)) - AlphaChannel.toNat src.a))
            (AlphaChannel.maxValue (RangeT := RangeT))) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_toNat_eq_min (RangeT := RangeT) dst src)

/-- For `dst + src`, source alpha is `0`, so output alpha is destination alpha. -/
lemma pixelRGBA_add_alpha_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).a = dst.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_src_zero (RangeT := RangeT) dst src hsrc)

/-- For `dst + src`, destination alpha is `0`, so output alpha is source alpha. -/
lemma pixelRGBA_add_alpha_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (dst + src).a = src.a := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_dst_zero (RangeT := RangeT) dst src hdst)

/-- For `dst + src`, source alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_add_alpha_src_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (dst + src).a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_src_full (RangeT := RangeT) dst src hsrc)

/-- For `dst + src`, destination alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_add_alpha_dst_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (dst + src).a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_dst_full (RangeT := RangeT) dst src hdst)

/-- For `dst + src`, both input alphas are `0`, so output alpha is `0`. -/
lemma pixelRGBA_add_alpha_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst + src).a = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_add_eq_rgbaOver] using
    (rgbaOver_alpha_zero_zero (RangeT := RangeT) dst src hdst hsrc)

/-- For `dst * src`, source alpha is `0`, so output alpha is destination alpha. -/
lemma pixelRGBA_mul_alpha_src_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).a = dst.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_src_zero (RangeT := RangeT) dst src hsrc)

/-- For `dst * src`, destination alpha is `0`, so output alpha is source alpha. -/
lemma pixelRGBA_mul_alpha_dst_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0) :
    (dst * src).a = src.a := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_dst_zero (RangeT := RangeT) dst src hdst)

/-- For `dst * src`, source alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_mul_alpha_src_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hsrc : src.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (dst * src).a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_src_full (RangeT := RangeT) dst src hsrc)

/-- For `dst * src`, destination alpha is maximal, so output alpha is maximal. -/
lemma pixelRGBA_mul_alpha_dst_full {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT))) :
    (dst * src).a = Nat.cast (R := RangeT) (AlphaChannel.maxValue (RangeT := RangeT)) := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_dst_full (RangeT := RangeT) dst src hdst)

/-- For `dst * src`, both input alphas are `0`, so output alpha is `0`. -/
lemma pixelRGBA_mul_alpha_zero_zero {RangeT : Type u} [AlphaChannel RangeT]
    [LawfulAlphaChannel RangeT] (dst src : PixelRGBA RangeT)
    (hdst : dst.a = Nat.cast (R := RangeT) 0)
    (hsrc : src.a = Nat.cast (R := RangeT) 0) :
    (dst * src).a = Nat.cast (R := RangeT) 0 := by
  simpa [pixelRGBA_mul_eq_rgbaMultiplyOver] using
    (rgbaMultiplyOver_alpha_zero_zero (RangeT := RangeT) dst src hdst hsrc)

end Lemmas

end Bitmaps
