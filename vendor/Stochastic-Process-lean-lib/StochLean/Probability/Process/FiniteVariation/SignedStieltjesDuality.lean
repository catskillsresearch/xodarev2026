/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.PredictableStieltjesDuality
public import StochLean.Probability.Process.Measurability.PredictableSignedKernelDuality

/-! # Signed tests for the actual increasing-process Stieltjes kernels

The actual martingale difference gives equality on predictable rectangles.
The signed kernel theorem then transfers absolute integrability and proves
the expected Stieltjes-integral equality. A finite expected signed Bochner
value alone is not used as an integrability condition.

The kernels here are the existing actual path-variation measures of increasing
processes. They have no atom at zero, and the original initial values remain
arbitrary. This is an ordinary signed Stieltjes test, not a Chapter IV
stochastic integral of arbitrary predictable processes.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X Y : ℝ≥0 → Ω → ℝ}

/-- Actual signed Stieltjes duality, including integrability under both
composition-product measures. Only the source's expected absolute integral
is an input, and only the source needs global integrable variation. -/
theorem integral_integral_totalVariationKernel_eq_of_martingale_sub
    (haX : Adapted F X) (hvX : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hrX : ∀ ω, IsRightContinuousPath (X · ω)) (hmX : ∀ ω, Monotone (X · ω))
    (haY : Adapted F Y) (hvY : ∀ ω, LocallyBoundedVariationOn (Y · ω) univ)
    (hrY : ∀ ω, IsRightContinuousPath (Y · ω)) (hmY : ∀ ω, Monotone (Y · ω))
    (hiX : ∀ t, Integrable (X t) P) (hiY : ∀ t, Integrable (Y t) P)
    (hX : HasIntegrableVariation X P) (hM : Martingale (X - Y) F P)
    {H : ℝ≥0 × Ω → ℝ} (hH : Measurable[F.predictable] H)
    (habs : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal ‖H (t, ω)‖
      ∂totalVariationKernel X haX hvX hrX ω ∂P) < ∞) :
    Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1))
        (P ⊗ₘ totalVariationKernel X haX hvX hrX) ∧
      Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1))
        (P ⊗ₘ totalVariationKernel Y haY hvY hrY) ∧
      (∫ ω, ∫ t, H (t, ω) ∂totalVariationKernel X haX hvX hrX ω ∂P) =
        ∫ ω, ∫ t, H (t, ω) ∂totalVariationKernel Y haY hvY hrY ω ∂P := by
  let := isSFiniteKernel_totalVariationKernel haX hvX hrX
  let := isSFiniteKernel_totalVariationKernel haY hvY hrY
  apply Kernel.integral_integral_eq_of_predictable_rectangles F
    (hX.lintegral_totalVariationKernel_univ_lt_top haX hvX hrX) _ _ hH habs
  · intro E _
    have hzeroX (ω : Ω) : totalVariationKernel X haX hvX hrX ω {0} = 0 :=
      variationStieltjes_measure_zero _
    have hzeroY (ω : Ω) : totalVariationKernel Y haY hvY hrY ω {0} = 0 :=
      variationStieltjes_measure_zero _
    simp only [hzeroX, hzeroY]
  · intro s t E hE
    by_cases hst : s ≤ t
    · exact lintegral_totalVariationKernel_Ioc_eq_of_martingale_sub
        haX hvX hrX hmX haY hvY hrY hmY hiX hiY hM hst hE
    · simp only [Ioc_eq_empty_of_le (le_of_not_ge hst), measure_empty]

end ProbabilityTheory
