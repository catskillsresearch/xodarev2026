/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Probability.Process.Semimartingale.Stricker

/-! # Filtration transport of the source elementary integral process -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F G : Filtration ℝ≥0 mΩ}

theorem IsSimplePredictable.elementaryIntegralProcess_monoFiltration
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (hFG : ∀ t, F t ≤ G t)
    (X : ℝ≥0 → Ω → ℝ) :
    (hH.monoFiltration hFG).elementaryIntegralProcess X = hH.elementaryIntegralProcess X := by
  funext t
  exact hH.elementaryIntegral_monoFiltration hFG (fun s ω ↦ X (min s t) ω)

end ProbabilityTheory
