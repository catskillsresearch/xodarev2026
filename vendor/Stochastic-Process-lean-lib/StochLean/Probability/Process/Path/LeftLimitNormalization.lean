/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.Probability.Process.Path.Subtraction
public import StochLean.Probability.Process.Stopping.IntegrandAE

/-! # Source left limits of left-continuous processes

The only difference from the original process is its time-zero spike.
The statement uses one common event for all times.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

theorem IsLeftContinuousPath.leftLimitProcess_eq {ω : Ω}
    (h : IsLeftContinuousPath (X · ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    leftLimitProcess X t ω = X t ω := by
  simp only [leftLimitProcess, if_neg ht]
  exact (h t).leftLim_eq

theorem HasLeftContinuousPaths.leftLimitProcess_eq_sub_cutoff_zero
    (hX : HasLeftContinuousPaths X P) :
    Indistinguishable (leftLimitProcess X)
      (X - cutoffIntegrand X (fun _ ↦ (0 : WithTop ℝ≥0))) P := by
  filter_upwards [hX] with ω hω t
  by_cases ht : t = 0
  · subst t
    simp
  · rw [hω.leftLimitProcess_eq ht]
    have ht' : ¬ (t : WithTop ℝ≥0) ≤ 0 :=
      not_le_of_gt (WithTop.coe_lt_coe.mpr (pos_iff_ne_zero.mpr ht))
    simp only [Pi.sub_apply, cutoffIntegrand, if_neg ht', sub_zero]

theorem HasCagladPaths.hasCagladPaths_leftLimitProcess (hX : HasCagladPaths X P) :
    HasCagladPaths (leftLimitProcess X) P :=
  HasCagladPaths.congr hX.hasLeftContinuousPaths.leftLimitProcess_eq_sub_cutoff_zero.symm
    (hX.sub (hX.cutoffIntegrand _))

end ProbabilityTheory
