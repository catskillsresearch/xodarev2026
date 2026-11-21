/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess

/-! # Event masks in the source integrator

These exact finite-sum identities include the initial product and require no
measurability, path regularity or semimartingale hypothesis on the integrator.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {H : ℝ≥0 → Ω → ℝ}

theorem SimplePredictableRep.integral_indicator_integrator
    (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) (s : Set Ω) :
    H.integral (fun t ↦ s.indicator (X t)) = s.indicator (H.integral X) := by
  classical
  funext ω
  by_cases hs : ω ∈ s <;> simp [SimplePredictableRep.integral, hs]

theorem IsSimplePredictable.elementaryIntegral_indicator_integrator
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (s : Set Ω) :
    hH.elementaryIntegral (fun t ↦ s.indicator (X t)) = s.indicator (hH.elementaryIntegral X) :=
  hH.choose.integral_indicator_integrator X s

theorem IsSimplePredictable.elementaryIntegralProcess_indicator_integrator
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (s : Set Ω) :
    hH.elementaryIntegralProcess (fun t ↦ s.indicator (X t)) =
      fun t ↦ s.indicator (hH.elementaryIntegralProcess X t) := by
  funext t
  exact hH.elementaryIntegral_indicator_integrator (fun u ω ↦ X (min u t) ω) s

end ProbabilityTheory
