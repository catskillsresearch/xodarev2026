/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LeftStepBounds
public import StochLean.Analysis.PathVariation.Reflection
public import StochLean.Analysis.PathVariation.StepIntegral

/-! # Sampling a right-continuous interval step moves its endpoints upwards

Ceilings use the original partition points and are capped at its horizon.
Repeated endpoints are allowed. The increment identity is valid for every
integrator, before any right-continuity or semimartingale assumption.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem ceilingPoint_lt_iff_of_mem_cell (π : TimePartition T) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) (a : ℝ≥0) :
    π.ceilingPoint a < t ↔ a ≤ π.left i := by
  constructor
  · intro ha
    rcases π.endpoint_le_left_or_right_le (π.ceilingPoint_mem a) i with h | h
    · have hm : min a T ≤ π.left i := (π.min_le_ceilingPoint a).trans h
      rcases min_le_iff.mp hm with hleft | hT
      · exact hleft
      · exact False.elim (not_lt_of_ge hT
          (hi.1.trans_le (hi.2.trans (π.point_le_horizon _))))
    · exact False.elim (not_lt_of_ge (hi.2.trans h) ha)
  · intro ha
    exact (π.monotone_point (π.ceilingIndex_le ((min_le_left a T).trans ha))).trans_lt hi.1

theorem le_ceilingPoint_iff_of_mem_cell (π : TimePartition T) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) (a : ℝ≥0) :
    t ≤ π.ceilingPoint a ↔ π.left i < a := by
  simpa only [not_lt, not_le] using not_congr (π.ceilingPoint_lt_iff_of_mem_cell hi a)

theorem leftStep_step_Ico (π : TimePartition T) (a b : ℝ≥0) (c : ℝ)
    {t : ℝ≥0} (ht : 0 < t) :
    π.leftStep (fun u ↦ if a ≤ u ∧ u < b then c else 0) t =
      if π.ceilingPoint a < t ∧ t ≤ π.ceilingPoint b then c else 0 := by
  by_cases htT : t ≤ T
  · obtain ⟨i, hi⟩ := π.exists_cell ⟨ht, htT⟩
    rw [π.leftStep_eq_of_mem_cell _ hi]
    simp only [π.ceilingPoint_lt_iff_of_mem_cell hi a, π.le_ceilingPoint_iff_of_mem_cell hi b]
  · rw [π.leftStep_eq_zero_of_horizon_lt _ (lt_of_not_ge htT)]
    have hb : ¬ t ≤ π.ceilingPoint b := fun h ↦ htT (h.trans (π.ceilingPoint_le_horizon b))
    simp only [hb, and_false, if_false]

theorem sum_increment_step_Ico (π : TimePartition T) {a b : ℝ≥0} (hab : a ≤ b)
    (c : ℝ) (x : ℝ≥0 → ℝ) :
    (∑ i : Fin π.size, (if a ≤ π.left i ∧ π.left i < b then c else 0) *
      (x (π.right i) - x (π.left i))) = c * (x (π.ceilingPoint b) - x (π.ceilingPoint a)) := by
  classical
  have heq := StochLean.sum_intervalIncrement_congr
    π.left π.right (fun i ↦ if a ≤ π.left i ∧ π.left i < b then c else 0)
    (fun _ : Unit ↦ π.ceilingPoint a) (fun _ : Unit ↦ π.ceilingPoint b) (fun _ : Unit ↦ c)
    π.left_le_right (fun _ ↦ π.ceilingPoint_mono hab) (fun t ht ↦ ?_) x
  · simpa only [Fintype.sum_unique] using heq
  · simpa only [leftStep, if_neg (ne_of_gt ht), Set.indicator_apply, Set.mem_Ioc,
      Fintype.sum_unique] using π.leftStep_step_Ico a b c ht

theorem ceilingPoint_tendsto_nhdsGE_of_eventually_le {U : ℕ → ℝ≥0}
    (π : (n : ℕ) → TimePartition (U n)) (a : ℝ≥0)
    (hU : ∀ᶠ n in atTop, a ≤ U n)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).ceilingPoint a) atTop (𝓝[≥] a) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
      (hU.mono fun _ hn ↦ (π _).dist_ceilingPoint_le_mesh hn) hmesh
  · filter_upwards [hU] with n hn
    simpa only [Set.mem_Ici, min_eq_left hn] using (π n).min_le_ceilingPoint a

end StochLean.TimePartition
