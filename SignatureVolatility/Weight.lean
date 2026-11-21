module

public import Mathlib


@[expose] public section

namespace SignatureVolatility

structure Weight where
  toFun : ℕ → ℝ
  w_zero : toFun 0 = 1
  pos : ∀ n : ℕ, 0 < toFun n
  mono : Monotone toFun

instance : CoeFun Weight (fun _ => ℕ → ℝ) := ⟨Weight.toFun⟩

namespace Weight

lemma one_le (w : Weight) (n : ℕ) : 1 ≤ w n := by
  rw [← w.w_zero]
  exact w.mono (Nat.zero_le n)

lemma inv_le_one (w : Weight) (n : ℕ) : (w n)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (w.one_le n)

end Weight

end SignatureVolatility
