/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimitNormalization
public import StochLean.Probability.Process.Filtration.Usual

/-! # Adaptedness of source left limits of left-continuous processes -/

@[expose] public section

open ProbabilityTheory
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Adapted.leftLimitProcess_of_leftContinuous_usual (ha : Adapted F X)
    (hF : F.IsUsual P) (hr : HasLeftContinuousPaths X P) :
    Adapted F (leftLimitProcess X) := by
  have heq := hr.leftLimitProcess_eq_sub_cutoff_zero
  have haK := adapted_cutoffIntegrand ha (isStoppingTime_const F 0)
  intro t
  have hcomplete : IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  exact hcomplete.measurable_congr_ae ((ha t).sub (haK t))
    (heq.symm.mono fun _ hω ↦ hω t)

end MeasureTheory
