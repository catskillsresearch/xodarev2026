/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Oscillation
public import Mathlib.Data.Finset.Max

/-!
# Endpoint approximations for finite partitions

The right endpoint projection is monotone, remains in the original endpoint
set, and is at distance at most the mesh on the compact horizon. This is a
deterministic approximation: no extra grid is inserted.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

/-- Extend the finite endpoint list constantly after its last index. -/
def pointNat (π : TimePartition T) (n : ℕ) : ℝ≥0 :=
  π.point ⟨min n π.size, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem pointNat_mono (π : TimePartition T) : Monotone π.pointNat := by
  intro n m hnm
  apply π.monotone_point
  exact min_le_min_right _ hnm

theorem pointNat_fin (π : TimePartition T) (i : Fin (π.size + 1)) :
    π.pointNat i = π.point i := by
  simp only [pointNat, min_eq_left (Nat.le_of_lt_succ i.isLt)]

theorem pointNat_mem (π : TimePartition T) (n : ℕ) : π.pointNat n ∈ Set.range π.point :=
  ⟨_, rfl⟩

theorem image_pointNat_Iic (π : TimePartition T) :
    π.pointNat '' Iic π.size = Set.range π.point := by
  ext t
  constructor
  · rintro ⟨n, _, rfl⟩
    exact π.pointNat_mem n
  · rintro ⟨i, rfl⟩
    exact ⟨i, Nat.le_of_lt_succ i.isLt, π.pointNat_fin i⟩

/-- Indices at or above the requested time, truncated to the horizon. -/
noncomputable def upperIndices (π : TimePartition T) (t : ℝ≥0) :
    Finset (Fin (π.size + 1)) :=
  Finset.univ.filter fun i ↦ min t T ≤ π.point i

theorem upperIndices_nonempty (π : TimePartition T) (t : ℝ≥0) :
    (upperIndices π t).Nonempty := by
  classical
  exact ⟨Fin.last π.size, by simp [upperIndices, π.last_eq_horizon]⟩

noncomputable def ceilingIndex (π : TimePartition T) (t : ℝ≥0) : Fin (π.size + 1) :=
  (upperIndices π t).min' (upperIndices_nonempty π t)

noncomputable def ceilingPoint (π : TimePartition T) (t : ℝ≥0) : ℝ≥0 :=
  π.point (π.ceilingIndex t)

theorem min_le_ceilingPoint (π : TimePartition T) (t : ℝ≥0) :
    min t T ≤ π.ceilingPoint t := by
  have h := Finset.min'_mem (upperIndices π t) (upperIndices_nonempty π t)
  simpa only [upperIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    ceilingPoint, ceilingIndex] using h

theorem ceilingIndex_le (π : TimePartition T) {t : ℝ≥0} {i : Fin (π.size + 1)}
    (hi : min t T ≤ π.point i) : π.ceilingIndex t ≤ i := by
  classical
  unfold ceilingIndex
  apply Finset.min'_le
  simp only [upperIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hi

theorem ceilingIndex_mono (π : TimePartition T) : Monotone π.ceilingIndex := by
  intro s t hst
  exact π.ceilingIndex_le ((min_le_min_right T hst).trans (π.min_le_ceilingPoint t))

theorem ceilingPoint_mono (π : TimePartition T) : Monotone π.ceilingPoint :=
  π.monotone_point.comp π.ceilingIndex_mono

theorem ceilingPoint_le_horizon (π : TimePartition T) (t : ℝ≥0) :
    π.ceilingPoint t ≤ T := π.point_le_horizon _

theorem ceilingPoint_mem (π : TimePartition T) (t : ℝ≥0) :
    π.ceilingPoint t ∈ Set.range π.point := ⟨_, rfl⟩

theorem dist_ceilingPoint_le_mesh (π : TimePartition T) {t : ℝ≥0} (ht : t ≤ T) :
    dist (π.ceilingPoint t) t ≤ (π.mesh : ℝ) := by
  have htc : t ≤ π.ceilingPoint t := by simpa [min_eq_left ht] using π.min_le_ceilingPoint t
  by_cases hzero : π.ceilingIndex t = 0
  · have hc : π.ceilingPoint t = 0 := by simp [ceilingPoint, hzero, π.first_eq_zero]
    have ht0 : t = 0 := le_antisymm (htc.trans_eq hc) bot_le
    rw [hc, ht0, dist_self]
    exact NNReal.coe_nonneg _
  · let i : Fin π.size := (π.ceilingIndex t).pred hzero
    have hir : π.right i = π.ceilingPoint t := by simp [right, i, ceilingPoint]
    have hil : π.left i < t := by
      apply lt_of_not_ge
      intro hle
      have hmin := π.ceilingIndex_le (i := i.castSucc) ((min_le_left t T).trans hle)
      have hlt : i.castSucc < π.ceilingIndex t := by
        simpa [i] using (Fin.castSucc_lt_succ (i := i))
      exact (not_le_of_gt hlt) hmin
    calc
      dist (π.ceilingPoint t) t ≤ dist (π.right i) (π.left i) := by
        rw [hir, NNReal.dist_eq, NNReal.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast htc)),
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (hil.le.trans htc)))]
        exact sub_le_sub_left (by exact_mod_cast hil.le) _
      _ = (π.gap i : ℝ) := π.dist_right_left_eq_gap i
      _ ≤ π.mesh := by exact_mod_cast π.gap_le_mesh i

theorem ceilingPoint_tendsto {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) {t : ℝ≥0} (ht : t ≤ T) :
    Tendsto (fun n ↦ (π n).ceilingPoint t) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (π n).dist_ceilingPoint_le_mesh ht) hmesh

end StochLean.TimePartition
