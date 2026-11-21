/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StrictApproximation

/-! # Sampling left-continuous interval steps and the initial spike

An `Ioc` step uses strictly upper projected endpoints. The separate initial
spike spreads only over the first positive cell. All identities are pathwise.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem strictCeilingPoint_lt_iff_of_mem_cell (π : TimePartition T) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) (a : ℝ≥0) :
    π.strictCeilingPoint a < t ↔ a < π.left i := by
  constructor
  · intro ha
    rcases π.endpoint_le_left_or_right_le (π.strictCeilingPoint_mem a) i with h | h
    · rcases π.strictCeilingPoint_spec a with hlt | heq
      · exact hlt.trans_le h
      · exact False.elim (not_lt_of_ge (hi.2.trans (π.point_le_horizon _))
          (heq ▸ ha))
    · exact False.elim (not_lt_of_ge (hi.2.trans h) ha)
  · intro ha
    exact (π.monotone_point (π.strictCeilingIndex_le (Or.inl ha))).trans_lt hi.1

theorem le_strictCeilingPoint_iff_of_mem_cell (π : TimePartition T) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) (a : ℝ≥0) :
    t ≤ π.strictCeilingPoint a ↔ π.left i ≤ a := by
  simpa only [not_lt] using not_congr (π.strictCeilingPoint_lt_iff_of_mem_cell hi a)

theorem leftStep_step_Ioc (π : TimePartition T) (a b : ℝ≥0) (c : ℝ)
    {t : ℝ≥0} (ht : 0 < t) :
    π.leftStep (fun u ↦ if a < u ∧ u ≤ b then c else 0) t =
      if π.strictCeilingPoint a < t ∧ t ≤ π.strictCeilingPoint b then c else 0 := by
  by_cases htT : t ≤ T
  · obtain ⟨i, hi⟩ := π.exists_cell ⟨ht, htT⟩
    rw [π.leftStep_eq_of_mem_cell _ hi]
    simp only [π.strictCeilingPoint_lt_iff_of_mem_cell hi a,
      π.le_strictCeilingPoint_iff_of_mem_cell hi b]
  · rw [π.leftStep_eq_zero_of_horizon_lt _ (lt_of_not_ge htT)]
    have hb : ¬ t ≤ π.strictCeilingPoint b :=
      fun h ↦ htT (h.trans (π.strictCeilingPoint_le_horizon b))
    simp only [hb, and_false, if_false]

theorem sum_increment_step_Ioc (π : TimePartition T) {a b : ℝ≥0} (hab : a ≤ b)
    (c : ℝ) (x : ℝ≥0 → ℝ) :
    (∑ i : Fin π.size, (if a < π.left i ∧ π.left i ≤ b then c else 0) *
      (x (π.right i) - x (π.left i))) =
        c * (x (π.strictCeilingPoint b) - x (π.strictCeilingPoint a)) := by
  classical
  have heq := StochLean.sum_intervalIncrement_congr
    π.left π.right (fun i ↦ if a < π.left i ∧ π.left i ≤ b then c else 0)
    (fun _ : Unit ↦ π.strictCeilingPoint a) (fun _ : Unit ↦ π.strictCeilingPoint b)
    (fun _ : Unit ↦ c) π.left_le_right (fun _ ↦ π.strictCeilingPoint_mono hab)
    (fun t ht ↦ ?_) x
  · simpa only [Fintype.sum_unique] using heq
  · simpa only [leftStep, if_neg (ne_of_gt ht), Set.indicator_apply, Set.mem_Ioc,
      Fintype.sum_unique] using π.leftStep_step_Ioc a b c ht

theorem leftStep_initial_spike (π : TimePartition T) (c : ℝ)
    {t : ℝ≥0} (ht : 0 < t) :
    π.leftStep (fun u ↦ if u = 0 then c else 0) t =
      if 0 < t ∧ t ≤ π.strictCeilingPoint 0 then c else 0 := by
  by_cases htT : t ≤ T
  · obtain ⟨i, hi⟩ := π.exists_cell ⟨ht, htT⟩
    rw [π.leftStep_eq_of_mem_cell _ hi]
    simp only [π.le_strictCeilingPoint_iff_of_mem_cell hi 0, ht, true_and,
      nonpos_iff_eq_zero]
  · rw [π.leftStep_eq_zero_of_horizon_lt _ (lt_of_not_ge htT)]
    have hb : ¬ t ≤ π.strictCeilingPoint 0 :=
      fun h ↦ htT (h.trans (π.strictCeilingPoint_le_horizon 0))
    simp only [hb, and_false, if_false]

theorem sum_increment_initial_spike (π : TimePartition T) (c : ℝ) (x : ℝ≥0 → ℝ) :
    (∑ i : Fin π.size, (if π.left i = 0 then c else 0) *
      (x (π.right i) - x (π.left i))) = c * (x (π.strictCeilingPoint 0) - x 0) := by
  classical
  have heq := StochLean.sum_intervalIncrement_congr
    π.left π.right (fun i ↦ if π.left i = 0 then c else 0)
    (fun _ : Unit ↦ 0) (fun _ : Unit ↦ π.strictCeilingPoint 0) (fun _ : Unit ↦ c)
    π.left_le_right (fun _ ↦ bot_le) (fun t ht ↦ ?_) x
  · simpa only [Fintype.sum_unique] using heq
  · simpa only [leftStep, if_neg (ne_of_gt ht), Set.indicator_apply, Set.mem_Ioc,
      Fintype.sum_unique] using π.leftStep_initial_spike c ht

end StochLean.TimePartition
