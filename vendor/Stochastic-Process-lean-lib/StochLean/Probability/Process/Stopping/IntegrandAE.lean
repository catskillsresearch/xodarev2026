/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Integrand

/-! # Common-event cutoff regularity and invariance -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {H K : ℝ≥0 → Ω → ℝ}

theorem HasCagladPaths.cutoffIntegrand (hH : HasCagladPaths H P)
    (τ : Ω → WithTop ℝ≥0) : HasCagladPaths (cutoffIntegrand H τ) P := by
  filter_upwards [hH] with ω hω
  exact isCagladPath_cutoffIntegrand (H := fun t (_ : Unit) ↦ H t ω)
    (fun _ ↦ hω) (fun _ ↦ τ ω) ()

theorem Indistinguishable.cutoffIntegrand (hHK : Indistinguishable H K P)
    (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (cutoffIntegrand H τ) (cutoffIntegrand K τ) P := by
  filter_upwards [hHK] with ω hω t
  simp only [ProbabilityTheory.cutoffIntegrand, hω]

end ProbabilityTheory
