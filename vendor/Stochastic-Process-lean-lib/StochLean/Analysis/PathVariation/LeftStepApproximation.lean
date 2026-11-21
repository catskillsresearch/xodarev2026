/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Approximation
public import StochLean.Analysis.PathVariation.PartialSums
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Left-endpoint step approximation on a finite partition

Cells are left-open and right-closed. Repeated endpoints are permitted: every
positive time before the horizon belongs to exactly one nonempty cell.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem exists_cell (π : TimePartition T) {t : ℝ≥0} (ht : t ∈ Ioc 0 T) :
    ∃ i : Fin π.size, π.left i < t ∧ t ≤ π.right i := by
  have htc : t ≤ π.ceilingPoint t := by
    simpa only [min_eq_left ht.2] using π.min_le_ceilingPoint t
  have hzero : π.ceilingIndex t ≠ 0 := by
    intro hz
    have hc : π.ceilingPoint t = 0 := by simp only [ceilingPoint, hz, π.first_eq_zero]
    exact not_lt_of_ge (htc.trans_eq hc) ht.1
  let i : Fin π.size := (π.ceilingIndex t).pred hzero
  have hir : π.right i = π.ceilingPoint t := by simp [right, i, ceilingPoint]
  refine ⟨i, ?_, hir ▸ htc⟩
  apply lt_of_not_ge
  intro hle
  have hmin := π.ceilingIndex_le (i := i.castSucc) ((min_le_left t T).trans hle)
  have hlt : i.castSucc < π.ceilingIndex t := by
    simpa [i] using (Fin.castSucc_lt_succ (i := i))
  exact (not_le_of_gt hlt) hmin

theorem cell_unique (π : TimePartition T) {t : ℝ≥0} {i j : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) (hj : π.left j < t ∧ t ≤ π.right j) : i = j := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hji
    exact not_lt_of_ge (hj.2.trans (π.right_le_left_of_lt hji)) hi.1
  · apply le_of_not_gt
    intro hij
    exact not_lt_of_ge (hi.2.trans (π.right_le_left_of_lt hij)) hj.1

noncomputable def leftStep (π : TimePartition T) (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t = 0 then f 0 else
    ∑ i : Fin π.size, (Ioc (π.left i) (π.right i)).indicator (fun _ ↦ f (π.left i)) t

@[simp] theorem leftStep_zero (π : TimePartition T) (f : ℝ≥0 → ℝ) : π.leftStep f 0 = f 0 := by
  simp only [leftStep, ↓reduceIte]

theorem leftStep_eq_of_mem_cell (π : TimePartition T) (f : ℝ≥0 → ℝ) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) : π.leftStep f t = f (π.left i) := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [leftStep, if_neg ht, Finset.sum_eq_single i]
  · exact indicator_of_mem (s := Ioc (π.left i) (π.right i)) (a := t) hi (fun _ ↦ f (π.left i))
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji (π.cell_unique hj hi)
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

theorem dist_left_of_mem_cell_le_mesh (π : TimePartition T) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) : dist t (π.left i) ≤ (π.mesh : ℝ) := by
  calc
    dist t (π.left i) ≤ dist (π.right i) (π.left i) := by
      rw [NNReal.dist_eq, NNReal.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hi.1.le)),
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast π.left_le_right i))]
      exact sub_le_sub_right (by exact_mod_cast hi.2) _
    _ = (π.gap i : ℝ) := π.dist_right_left_eq_gap i
    _ ≤ π.mesh := by exact_mod_cast π.gap_le_mesh i

theorem tendstoUniformlyOn_leftStep {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n ↦ (π n).leftStep f) f atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa only [leftStep_zero, dist_self] using hε
  · obtain ⟨i, hi⟩ := (π n).exists_cell ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), ht.2⟩
    rw [(π n).leftStep_eq_of_mem_cell f hi]
    exact hmod t ht ((π n).left i) ⟨bot_le, (π n).point_le_horizon _⟩
      (((π n).dist_left_of_mem_cell_le_mesh hi).trans_lt hn)

end StochLean.TimePartition
