/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Probability.Process.Equivalence

/-! # Source integral invariance under indistinguishable integrators -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

theorem IsSimplePredictable.elementaryIntegralProcess_congr_integrator
    (hH : IsSimplePredictable H F) (hXY : Indistinguishable X Y P) :
    Indistinguishable (hH.elementaryIntegralProcess X) (hH.elementaryIntegralProcess Y) P := by
  rw [hH.elementaryIntegralProcess_eq hH.choose hH.choose_spec X,
    hH.elementaryIntegralProcess_eq hH.choose hH.choose_spec Y]
  filter_upwards [hXY] with ω hω t
  simp only [SimplePredictableRep.integralProcess_apply, hω]

end ProbabilityTheory
