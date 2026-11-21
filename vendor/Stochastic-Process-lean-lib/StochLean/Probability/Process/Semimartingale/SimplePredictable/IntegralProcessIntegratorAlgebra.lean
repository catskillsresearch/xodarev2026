/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess

/-! # Linearity of the elementary integral process in its integrator -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {H : ℝ≥0 → Ω → ℝ}

theorem IsSimplePredictable.elementaryIntegralProcess_add_integrator
    (hH : IsSimplePredictable H F) (X Y : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (X + Y) =
      hH.elementaryIntegralProcess X + hH.elementaryIntegralProcess Y := by
  funext t
  exact hH.elementaryIntegral_add_integrator (fun s ω ↦ X (min s t) ω)
    (fun s ω ↦ Y (min s t) ω)

theorem IsSimplePredictable.elementaryIntegralProcess_const_mul_integrator
    (hH : IsSimplePredictable H F) (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (fun t ω ↦ c * X t ω) = c • hH.elementaryIntegralProcess X := by
  funext t
  exact hH.elementaryIntegral_const_mul_integrator c (fun s ω ↦ X (min s t) ω)

theorem IsSimplePredictable.elementaryIntegralProcess_neg_integrator
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (-X) = -hH.elementaryIntegralProcess X := by
  change hH.elementaryIntegralProcess (fun t ω ↦ -X t ω) = -hH.elementaryIntegralProcess X
  simpa only [neg_one_mul, neg_one_smul] using
    hH.elementaryIntegralProcess_const_mul_integrator (-1) X

theorem IsSimplePredictable.elementaryIntegralProcess_sub_integrator
    (hH : IsSimplePredictable H F) (X Y : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (X - Y) =
      hH.elementaryIntegralProcess X - hH.elementaryIntegralProcess Y := by
  rw [sub_eq_add_neg, hH.elementaryIntegralProcess_add_integrator,
    hH.elementaryIntegralProcess_neg_integrator, sub_eq_add_neg]

end ProbabilityTheory
