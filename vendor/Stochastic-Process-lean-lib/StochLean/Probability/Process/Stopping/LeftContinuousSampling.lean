/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.Predictable
public import StochLean.Probability.Process.Path.Stopping

/-! # Stopping values of almost surely left-continuous adapted processes

Use the existing indistinguishable predictable version, then transport its
stopping value with relative completeness. No regularity of the original
exceptional trajectories is imposed.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

theorem Adapted.measurable_stoppedValue_of_leftContinuous_usual
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (ha : Adapted F X) (hF : F.IsUsual P) (hl : HasLeftContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Measurable[hτ.measurableSpace] (stoppedValue X τ) := by
  obtain ⟨Y, heq, hp, _⟩ := ha.exists_predictable_indistinguishable_of_hasLeftContinuousPaths hF hl
  have hc : IsCompleteSubMeasurableSpace P hτ.measurableSpace := fun s hs ↦
    hτ.le_measurableSpace_of_const_le (fun _ ↦ bot_le) s (hF.complete_initial s hs)
  exact hc.measurable_congr_ae (measurable_stoppedValue hp.isStronglyProgressive hτ)
    (heq.stoppedValue τ).symm

end MeasureTheory
