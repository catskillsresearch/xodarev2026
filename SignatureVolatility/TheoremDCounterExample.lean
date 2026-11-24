module

public import SignatureVolatility.Prop58BlackScholesDepthFalse

@[expose] public section

namespace SignatureVolatility

/-!
# Theorem D (paper Theorem 66), residual-expansion clause: counterexample

The residual expansion of Theorem 66 is stated under the hypothesis `N^*_S < ∞`. Under the paper's
Definition 55 that hypothesis fails for Black–Scholes, so the clause is vacuous there. The proved
GKW projection part is `theorem_D` in `TheoremD` (board label `Half_TheoremD`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P]

/-- The residual-expansion hypothesis `N^*_S < ∞` of Theorem 66 fails for Black–Scholes. -/
theorem theorem_D_residual_hypothesis_fails (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀)
    (hσ₀ : σ₀ ≠ 0) (B : MultiBrownian Ω P 1) :
    ¬ (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤ := by
  rw [blackScholes_completenessDepth_eq_top]; exact lt_irrefl _

end SignatureVolatility
