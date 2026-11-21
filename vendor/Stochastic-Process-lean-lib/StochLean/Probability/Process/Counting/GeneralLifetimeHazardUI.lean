/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardUniformIntegrability
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrablePullback

/-! # Uniform integrability for the hazard of an arbitrary lifetime

The original closed count minus the stopped hazard of its actual lifetime
law is the measure-preserving pullback of the canonical compensated count.
Its whole-halfline uniform integrability therefore follows from the actual
integrable envelope already proved on the lifetime space. No new hazard or
terminal envelope is selected, and zero and infinite lifetimes are allowed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0}

/-- The actual closed count minus the hazard of its pushforward lifetime law
is uniformly integrable over all finite times on the original sample space. -/
theorem uniformIntegrable_singleJump_sub_hazard_map (hτ : Measurable τ) :
    UniformIntegrable (fun (t : ℝ≥0) ω ↦
      (if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ t ω)
      1 P := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  exact (uniformIntegrable_singleJump_sub_hazard_unrestricted (P.map τ)).comp_measurePreserving
    (hτ.measurePreserving P) le_rfl ENNReal.one_ne_top

end ProbabilityTheory
