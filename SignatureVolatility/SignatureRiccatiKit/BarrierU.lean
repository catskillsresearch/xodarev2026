module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# B4a. Explicit bounded C^{1,2} barrier for `v₁ x → 0` as `x → +∞`
-/

@[expose] public section

noncomputable section

open Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

/-- Explicit barrier `u(r, y) = -β (s₀ - r - A/y)_+³`. -/
noncomputable def barrierU (s₀ β A r y : ℝ) : ℝ :=
  if A / s₀ < y ∧ A / y < s₀ - r then -β * (s₀ - r - A / y) ^ 3 else 0

lemma barrierU_terminal (s₀ β A y : ℝ) (hs₀ : 0 < s₀) (hA : 0 < A) :
    barrierU s₀ β A s₀ y = 0 := by
  sorry

lemma barrierU_initial_le {s₀ β A x : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β) (hA : 0 < A)
    (hx : 2 * A / s₀ ≤ x) :
    barrierU s₀ β A 0 x ≤ -β * (s₀ ^ 3 / 8) := by
  sorry

/-- Algebraic PDE inequality on the active region, once
`A ≥ max 2 (max (2 √(s₀³)) (2 √β s₀³))`.
The writeup's intermediate claim that the parenthesis is `≤ -9/8` is
false (it is `≤ -3/8`); the conclusion `PDE ≤ -(9/8) β v² ≤ 0` still holds. -/
lemma barrierU_pde_nonpos {s₀ β A r y : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β)
    (hA2 : 2 ≤ A) (hAs : 2 * Real.sqrt (s₀ ^ 3) ≤ A)
    (hAβ : 2 * Real.sqrt β * s₀ ^ 3 ≤ A)
    (hr0 : 0 ≤ r) (hrs : r ≤ s₀) (hy1 : A / s₀ < y) (hy2 : A / y < s₀ - r) :
    let v := s₀ - r - A / y
    let ur := 3 * β * v ^ 2
    let uy := -3 * β * v ^ 2 * (A / y ^ 2)
    let uyy := -6 * β * v * (A / y ^ 2) ^ 2 + 6 * β * v ^ 2 * (A / y ^ 3)
    ur + y ^ 2 * uy + (1 / 2 : ℝ) * uyy + (1 / 2 : ℝ) * uy ^ 2 ≤ 0 := by
  sorry

end SignatureVolatility
