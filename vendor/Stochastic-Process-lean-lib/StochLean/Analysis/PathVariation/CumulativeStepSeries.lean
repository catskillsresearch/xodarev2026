/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Topology.Order.StepCutoffLimits
public import StochLean.Probability.Process.Path.Cadlag
public import Mathlib.Analysis.Normed.Group.Tannery

/-! # One-sided limits and actual jumps of absolutely summable step series

The index type is arbitrary and activation times may repeat. Each jump
is the full sum of all coefficients activated at that time.
-/

@[expose] public section

open Set Filter Function ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

variable {ι : Type*} {w : ι → ℝ} (a : ι → ℝ≥0)

theorem isRightContinuousPath_tsum_stepCutoff (hw : Summable (fun i ↦ |w i|)) :
    IsRightContinuousPath (fun t ↦ ∑' i, if a i ≤ t then w i else 0) := by
  intro t
  exact tendsto_tsum_of_dominated_convergence hw
    (fun i ↦ tendsto_stepCutoff_right (a i) t (w i))
    (Eventually.of_forall (fun (u : ℝ≥0) i ↦ by split_ifs <;> simp [abs_nonneg]))

theorem tendsto_tsum_stepCutoff_left (hw : Summable (fun i ↦ |w i|)) (t : ℝ≥0) :
    Tendsto (fun u ↦ ∑' i, if a i ≤ u then w i else 0) (𝓝[<] t)
      (𝓝 (∑' i, if a i < t then w i else 0)) := by
  exact tendsto_tsum_of_dominated_convergence hw
    (fun i ↦ tendsto_stepCutoff_left (a i) t (w i))
    (Eventually.of_forall (fun (u : ℝ≥0) i ↦ by split_ifs <;> simp [abs_nonneg]))

theorem isCadlagPath_tsum_stepCutoff (hw : Summable (fun i ↦ |w i|)) :
    IsCadlagPath (fun t ↦ ∑' i, if a i ≤ t then w i else 0) :=
  ⟨isRightContinuousPath_tsum_stepCutoff a hw,
    fun t _ ↦ ⟨_, tendsto_tsum_stepCutoff_left a hw t⟩⟩

theorem tsum_stepCutoff_sub_leftLim (hw : Summable (fun i ↦ |w i|))
    {t : ℝ≥0} (ht : 0 < t) :
    (∑' i, if a i ≤ t then w i else 0) -
        leftLim (fun u ↦ ∑' i, if a i ≤ u then w i else 0) t =
      ∑' i : a ⁻¹' {t}, w i := by
  classical
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  rw [leftLim_eq_of_tendsto (tendsto_tsum_stepCutoff_left a hw t)]
  have hc : Summable (fun i ↦ if a i ≤ t then w i else 0) :=
    hw.of_abs.indicator {i | a i ≤ t}
  have ho : Summable (fun i ↦ if a i < t then w i else 0) :=
    hw.of_abs.indicator {i | a i < t}
  rw [← hc.tsum_sub ho, tsum_subtype]
  apply tsum_congr
  intro i
  by_cases hi : a i < t
  · simp [Set.indicator, hi, hi.le, ne_of_lt hi]
  · by_cases he : a i = t
    · simp [Set.indicator, he]
    · have hgt : t < a i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm he)
      simp [Set.indicator, hi, he, not_le.mpr hgt]

end StochLean
