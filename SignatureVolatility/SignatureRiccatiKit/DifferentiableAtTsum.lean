module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# C3a. A locally uniformly convergent series of entire functions is entire
-/

@[expose] public section

noncomputable section

open Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

/-- On each ball `Metric.ball z₀ 1`, a summable majorant of the form
`C exp ‖z‖` is z-independent, so the tsum is differentiable at `z₀`. -/
lemma differentiableAt_tsum_of_locallyUniform (term : ℕ → ℂ → ℂ)
    (hterm : ∀ n, Differentiable ℂ (term n)) {C : ℝ}
    (hbound : ∀ z : ℂ, Summable (fun n : ℕ => ‖term n z‖) ∧
      ∑' n : ℕ, ‖term n z‖ ≤ C * Real.exp ‖z‖)
    (z₀ : ℂ) :
    DifferentiableAt ℂ (fun z => ∑' n : ℕ, term n z) z₀ := by
  sorry

end SignatureVolatility
