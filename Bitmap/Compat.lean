import Init.Tactics
import Batteries.Control.ForInStep.Lemmas
import Batteries.Tactic.Init
import Batteries.Tactic.Lemma

universe u v w

namespace Nat

def bit (b : Bool) (n : Nat) : Nat :=
  2 * n + b.toNat

theorem bit_val (b : Bool) (n : Nat) : bit b n = 2 * n + b.toNat := rfl

@[elab_as_elim]
noncomputable def strong_induction_on (n : Nat) {p : Nat → Sort u}
    (h : (n : Nat) → ((m : Nat) → m < n → p m) → p n) :
    p n :=
  Nat.strongRecOn n h

end Nat

attribute [refl] Nat.le_refl

namespace List

theorem forIn_eq_bindList {m : Type u → Type v} {α β : Type u} [Monad m] [LawfulMonad m]
    (f : α → β → m (ForInStep β)) (l : List α) (init : β) :
    forIn l init f = ForInStep.run <$> (ForInStep.yield init).bindList f l := by
  induction l generalizing init <;> simp [*]
  congr
  ext (b | b) <;> simp

end List

namespace Bitmaps

/-- Binary congruence helper kept for Mathlib-free proof compatibility. -/
theorem congrArg₂ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β → γ)
    {a₁ a₂ : α} {b₁ b₂ : β} (ha : a₁ = a₂) (hb : b₁ = b₂) :
    f a₁ b₁ = f a₂ b₂ := by
  cases ha
  cases hb
  rfl

/-- Local Nat transitivity alias kept for Mathlib-free proof compatibility. -/
theorem lt_of_lt_of_le {a b c : Nat} (hab : a < b) (hbc : b ≤ c) : a < c :=
  Nat.lt_of_lt_of_le hab hbc

/-- Local Nat transitivity alias kept for Mathlib-free proof compatibility. -/
theorem lt_of_le_of_lt {a b c : Nat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  Nat.lt_of_le_of_lt hab hbc

/-- Local Nat strictness alias kept for Mathlib-free proof compatibility. -/
theorem lt_of_le_of_ne {a b : Nat} (hab : a ≤ b) (hne : a ≠ b) : a < b :=
  Nat.lt_of_le_of_ne hab hne

/-- Local Nat negated-order alias kept for Mathlib-free proof compatibility. -/
theorem not_lt_of_ge {a b : Nat} (h : a ≤ b) : ¬ b < a :=
  Nat.not_lt_of_ge h

/-- Local Nat reflexivity alias kept for Mathlib-free proof compatibility. -/
theorem le_rfl {a : Nat} : a ≤ a :=
  Nat.le_refl a

/-- Local Nat transitivity alias kept for Mathlib-free proof compatibility. -/
theorem le_trans {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

/-- Local Nat antisymmetry alias kept for Mathlib-free proof compatibility. -/
theorem le_antisymm {a b : Nat} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  Nat.le_antisymm hab hba

/-- Local Nat transitivity alias kept for Mathlib-free proof compatibility. -/
theorem lt_trans {a b c : Nat} (hab : a < b) (hbc : b < c) : a < c :=
  Nat.lt_trans hab hbc

/-- Local Nat inequality alias kept for Mathlib-free proof compatibility. -/
theorem ne_of_lt {a b : Nat} (hab : a < b) : a ≠ b :=
  Nat.ne_of_lt hab

/-- Local Nat negated-order alias kept for Mathlib-free proof compatibility. -/
theorem not_le_of_gt {a b : Nat} (hab : a > b) : ¬ a ≤ b :=
  Nat.not_le_of_gt hab

/-- Local Nat ordered split alias kept for Mathlib-free proof compatibility. -/
theorem lt_or_eq_of_le {a b : Nat} (hab : a ≤ b) : a < b ∨ a = b :=
  Nat.lt_or_eq_of_le hab

/-- Local Nat minimum alias kept for Mathlib-free proof compatibility. -/
theorem le_min {a b c : Nat} (hab : a ≤ b) (hac : a ≤ c) : a ≤ Nat.min b c :=
  Nat.le_min.mpr ⟨hab, hac⟩

end Bitmaps
