/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SpecialJumpCriterion
public import StochLean.Probability.Process.Measurability.RunningSupremumLocalIntegrability

/-! # The running-norm criterion on the classical semimartingale domain

The forward implication uses actual special canonical components. For the
converse, generic local integrability transfers from the original running
norm to the actual running jumps, and actual compensation of the classical
FV component constructs specialness. No decomposition is inferred from the
good-integrator predicate before the separate BD theorem is proved.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Protter III.37 on the classical domain, with the existing real running
norm supremum and native masked local integrability. Initial moments are
not imposed; the good-integrator converse remains a separate theorem. -/
theorem
    IsClassicalSemimartingale.isSpecialSemimartingale_iff_locally_integrable_denseRunningSupremum
    (hX : IsClassicalSemimartingale X F P) (hF : F.IsUsual P) :
    IsSpecialSemimartingale X F P ↔
      Locally (fun Y : ℝ≥0 → Ω → ℝ ↦ ∀ t, Integrable (Y t) P) F
        (fun t ω ↦ (denseRunningSupremum (fun s v ↦ ‖X s v‖) t ω).toReal) P := by
  constructor
  · exact fun h ↦ h.locally_integrable_denseRunningSupremum hF
  · intro hS
    exact hX.isSpecialSemimartingale_of_locally_integrable_runningJumpSupremum hF
      (hX.1.locally_integrable_runningJumpSupremum_of_denseRunningSupremum hF hX.2.1 hS)

end ProbabilityTheory
