/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.MarkedSingleJumpCompensator
public import StochLean.Probability.Process.Counting.CensoringLaw

/-! # The actual compensator under arbitrary dependent censoring

The observation is the minimum of arrival and censoring lifetimes. Its
mark assigns ties to the arrival. The actual arrival-marked observation
submeasure is identified with the original arrival law restricted to
arrival before or at censoring. The full observation law, not this
submeasure alone, supplies the at-risk survival denominator.

The theorem specializes the proved marked compensation result to the
original observed pair and its genuine usual natural filtration. Neither
independence, finite lifetimes nor a density is needed for this general
measure formula. Identifying a printed small-window crude rate with a
density of this cause submeasure is a separate analytic step.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

open Classical in
/-- The sole compensator of actual censored arrivals is the stopped
cause hazard, using the true restricted arrival law and observation survival. -/
theorem predictableCompensator_censoredCount_eq_stopped_cause_hazard
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {T U : Ω → WithTop ℝ≥0} (hT : Measurable T) (hU : Measurable U) :
    let X : Ω → WithTop ℝ≥0 := fun ω ↦ min (T ω) (U ω)
    let B : Set Ω := {ω | T ω ≤ U ω}
    let F := Filtration.natural _
      (stronglyMeasurable_markedSingleJumpCount (hT.min hU) (measurableSet_le hT hU))
    let hD := markedSingleJumpCount_compensator_domain
      (P := P) (hT.min hU) (measurableSet_le hT hU)
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ stoppedProcess
        (fun r (_ : Ω) ↦ (eCauseSpecificHazard (P.map X) ((P.restrict B).map T) r).toReal)
        X t ω)
      P.completion := by
  have he := (censored_arrival_submeasure_eq_and_le (P := P) hT hU).1
  have hcomp := predictableCompensator_markedSingleJumpCount_eq_stopped_cause_hazard
    (P := P) (hT.min hU) (measurableSet_le hT hU)
  dsimp only at he hcomp ⊢
  rw [he] at hcomp
  exact hcomp

end ProbabilityTheory
