module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# C3c. Differentiating the Gaussian product exponential under the integral
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `j`-th derivative at `0` of
`r ↦ ∫ exp(r (x + i √t y)) d(γ_t ⊗ γ_1)` is the corresponding moment. -/
lemma iteratedDeriv_integral_cexp_gaussianReal_prod (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv j (fun r : ℂ =>
      ∫ p : ℝ × ℝ,
        Complex.exp (r * ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)))
          ∂((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1))) 0 =
      ∫ p : ℝ × ℝ,
        ((p.1 : ℂ) + Complex.I * (Real.sqrt t : ℂ) * (p.2 : ℂ)) ^ j
          ∂((gaussianReal 0 (Real.toNNReal t)).prod (gaussianReal 0 1)) := by
  sorry

end SignatureVolatility
