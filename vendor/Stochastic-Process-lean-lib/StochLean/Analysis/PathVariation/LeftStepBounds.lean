/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LeftStepApproximation

/-! # Left-step bounds and approximation with varying horizons

Sampling uses only past values, including the initial value. Compact-uniform
approximation of a continuous function therefore needs eventual horizon coverage
and vanishing mesh, not nested partitions or a deterministic mesh rate.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem leftStep_eq_zero_of_horizon_lt (π : TimePartition T) (f : ℝ≥0 → ℝ)
    {t : ℝ≥0} (ht : T < t) : π.leftStep f t = 0 := by
  classical
  have ht0 : t ≠ 0 := ne_of_gt ((show (0 : ℝ≥0) ≤ T from bot_le).trans_lt ht)
  rw [leftStep, if_neg ht0]
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact not_le_of_gt ht (hi.2.trans (π.point_le_horizon _))

@[simp] theorem leftStep_zero_fun (π : TimePartition T) :
    π.leftStep (fun _ ↦ 0) = fun _ ↦ 0 := by
  funext t
  simp [leftStep]

theorem norm_leftStep_sub_le_of_bound (π : TimePartition T) (f g : ℝ≥0 → ℝ)
    {U t : ℝ≥0} {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ≤ U, ‖f u - g u‖ ≤ C)
    (ht : t ≤ U) : ‖π.leftStep f t - π.leftStep g t‖ ≤ C := by
  by_cases ht0 : t = 0
  · subst t
    simpa only [leftStep_zero] using hb 0 bot_le
  by_cases htT : t ≤ T
  · obtain ⟨i, hi⟩ := π.exists_cell ⟨pos_iff_ne_zero.mpr ht0, htT⟩
    rw [π.leftStep_eq_of_mem_cell f hi, π.leftStep_eq_of_mem_cell g hi]
    exact hb (π.left i) (hi.1.le.trans ht)
  · rw [π.leftStep_eq_zero_of_horizon_lt f (lt_of_not_ge htT),
      π.leftStep_eq_zero_of_horizon_lt g (lt_of_not_ge htT), sub_self, norm_zero]
    exact hC

theorem tendstoUniformlyOn_leftStep_of_eventually_le {U : ℕ → ℝ≥0}
    (π : (n : ℕ) → TimePartition (U n)) {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hU : ∀ᶠ n in atTop, T ≤ U n)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n ↦ (π n).leftStep f) f atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [hmesh.eventually_lt_const hδ, hU] with n hn hUn
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa only [leftStep_zero, dist_self] using hε
  · obtain ⟨i, hi⟩ := (π n).exists_cell ⟨pos_iff_ne_zero.mpr ht0, ht.2.trans hUn⟩
    rw [(π n).leftStep_eq_of_mem_cell f hi]
    exact hmod t ht ((π n).left i) ⟨bot_le, hi.1.le.trans ht.2⟩
      (((π n).dist_left_of_mem_cell_le_mesh hi).trans_lt hn)

end StochLean.TimePartition
