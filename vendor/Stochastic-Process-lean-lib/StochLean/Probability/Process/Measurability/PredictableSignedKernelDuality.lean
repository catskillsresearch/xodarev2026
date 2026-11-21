/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.PredictableKernelDuality
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Signed predictable kernel duality with actual absolute integrability

The existing nonnegative predictable duality transfers absolute integrability
from the first actual composition-product measure to the second one. Positive
and negative parts then give equality of genuine signed iterated integrals.

The input is a finite expected absolute integral, not a bound on a possibly
totalized signed Bochner integral. Both product integrals are proved integrable
before Fubini and signed decomposition are used. This is a kernel-level
ingredient for the corrected signed compensator test, not a new integral or
compensator definition.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- Expected predictable rectangle masses determine signed iterated integrals
on their actual absolute-integrability domain. Integrability of both original
composition-product functions is part of the conclusion. -/
theorem integral_integral_eq_of_predictable_rectangles
    (F : Filtration ℝ≥0 mΩ) {κ η : Kernel Ω ℝ≥0}
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hfin : (∫⁻ ω, κ ω univ ∂P) < ∞)
    (h0 : ∀ E, MeasurableSet[F 0] E →
      (∫⁻ ω in E, κ ω {0} ∂P) = ∫⁻ ω in E, η ω {0} ∂P)
    (hIoc : ∀ s t E, MeasurableSet[F s] E →
      (∫⁻ ω in E, κ ω (Ioc s t) ∂P) = ∫⁻ ω in E, η ω (Ioc s t) ∂P)
    {H : ℝ≥0 × Ω → ℝ} (hH : Measurable[F.predictable] H)
    (habs : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal ‖H (t, ω)‖ ∂κ ω ∂P) < ∞) :
    Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1)) (P ⊗ₘ κ) ∧
      Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1)) (P ⊗ₘ η) ∧
      (∫ ω, ∫ t, H (t, ω) ∂κ ω ∂P) = ∫ ω, ∫ t, H (t, ω) ∂η ω ∂P := by
  let f : Ω × ℝ≥0 → ℝ := fun p ↦ H (p.2, p.1)
  have hm : Measurable f := (hH.mono F.predictable_le_prod le_rfl).comp measurable_swap
  have hn : Measurable[F.predictable] (fun p ↦ ENNReal.ofReal ‖H p‖) :=
    ENNReal.measurable_ofReal.comp (continuous_norm.measurable.comp hH)
  have heNorm := lintegral_lintegral_eq_of_predictable_rectangles F hfin h0 hIoc hn
  have hi (ξ : Kernel Ω ℝ≥0) [IsSFiniteKernel ξ]
      (hb : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal ‖H (t, ω)‖ ∂ξ ω ∂P) < ∞) :
      Integrable f (P ⊗ₘ ξ) := by
    refine ⟨hm.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm, Measure.lintegral_compProd
      (f := fun p ↦ ENNReal.ofReal ‖f p‖) (ENNReal.measurable_ofReal.comp hm.norm)]
    exact hb
  have hiκ := hi κ habs
  have hiη := hi η (heNorm ▸ habs)
  have hePos := lintegral_lintegral_eq_of_predictable_rectangles F hfin h0 hIoc
    (ENNReal.measurable_ofReal.comp hH)
  have heNeg := lintegral_lintegral_eq_of_predictable_rectangles F hfin h0 hIoc
    (ENNReal.measurable_ofReal.comp (measurable_neg.comp hH))
  simp only [Function.comp_def] at hePos heNeg
  refine ⟨hiκ, hiη, ?_⟩
  rw [← Measure.integral_compProd hiκ, ← Measure.integral_compProd hiη,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiκ,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiη]
  rw [Measure.lintegral_compProd (f := fun p ↦ ENNReal.ofReal (f p))
      (ENNReal.measurable_ofReal.comp hm),
    Measure.lintegral_compProd (f := fun p ↦ ENNReal.ofReal (-f p))
      (ENNReal.measurable_ofReal.comp hm.neg),
    Measure.lintegral_compProd (f := fun p ↦ ENNReal.ofReal (f p))
      (ENNReal.measurable_ofReal.comp hm),
    Measure.lintegral_compProd (f := fun p ↦ ENNReal.ofReal (-f p))
      (ENNReal.measurable_ofReal.comp hm.neg)]
  change (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (H (t, ω)) ∂κ ω ∂P).toReal -
      (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (-H (t, ω)) ∂κ ω ∂P).toReal =
    (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (H (t, ω)) ∂η ω ∂P).toReal -
      (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (-H (t, ω)) ∂η ω ∂P).toReal
  rw [hePos, heNeg]

end ProbabilityTheory.Kernel
