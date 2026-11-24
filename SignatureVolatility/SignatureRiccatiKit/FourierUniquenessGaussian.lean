module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# C3b. Fourier uniqueness for an L¹ identity against a nondegenerate Gaussian
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- If the Fourier transform of `(f - G)` against `N(0, t)` vanishes for every
frequency, then `G x = (f x : ℂ)` for `gaussianReal 0 t`-a.e. `x`. -/
lemma ae_eq_of_fourier_zero_gaussianReal {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {G : ℂ → ℂ}
    (hfourier : ∀ ξ : ℝ,
      ∫ x : ℝ, ((f x : ℂ) - G x) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))
        ∂(gaussianReal 0 (Real.toNNReal t)) = 0) :
    ∀ᵐ x : ℝ ∂(gaussianReal 0 (Real.toNNReal t)), G x = (f x : ℂ) := by
  sorry

end SignatureVolatility
