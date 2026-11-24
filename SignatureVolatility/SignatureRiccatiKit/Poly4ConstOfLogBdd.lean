module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Degree-≤4 polynomial bounded above by 0 and below by `L - 2 log(1+s₀|x|)` on `(-∞,0]` is constant
-/

@[expose] public section

noncomputable section

open Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

/-- A degree-`≤ 4` polynomial bounded above by `0` and below by
`L - 2 log(1 + s₀ |x|)` on `(-∞, 0]` is constant. This is the Part 3
drop-in replacement for `poly4_const_of_bdd_nonpos`; the main theorem
statement is unchanged. -/
lemma poly4_const_of_log_bdd_nonpos {a₀ a₁ a₂ a₃ a₄ L s₀ : ℝ} (hs₀ : 0 < s₀)
    (hbdd : ∀ x : ℝ, x ≤ 0 →
      L - 2 * Real.log (1 + s₀ * |x|) ≤
        a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ∧
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ≤ 0) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 := by
  sorry

end SignatureVolatility
