/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LeftStepCeiling

/-! # Strict upper endpoint approximation

The first endpoint strictly above a time is used when sampling a left-continuous
interval step. The projection is capped at the horizon if there is no such
endpoint. Repeated endpoints and a zero horizon are allowed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

noncomputable def strictUpperIndices (π : TimePartition T) (t : ℝ≥0) :
    Finset (Fin (π.size + 1)) :=
  Finset.univ.filter fun i ↦ t < π.point i ∨ i = Fin.last π.size

theorem strictUpperIndices_nonempty (π : TimePartition T) (t : ℝ≥0) :
    (π.strictUpperIndices t).Nonempty := by
  classical
  exact ⟨Fin.last π.size, by simp [strictUpperIndices]⟩

noncomputable def strictCeilingIndex (π : TimePartition T) (t : ℝ≥0) : Fin (π.size + 1) :=
  (π.strictUpperIndices t).min' (π.strictUpperIndices_nonempty t)

noncomputable def strictCeilingPoint (π : TimePartition T) (t : ℝ≥0) : ℝ≥0 :=
  π.point (π.strictCeilingIndex t)

theorem strictCeilingIndex_spec (π : TimePartition T) (t : ℝ≥0) :
    t < π.strictCeilingPoint t ∨ π.strictCeilingIndex t = Fin.last π.size := by
  have h := Finset.min'_mem (π.strictUpperIndices t) (π.strictUpperIndices_nonempty t)
  simpa only [strictUpperIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    strictCeilingPoint, strictCeilingIndex] using h

theorem strictCeilingPoint_spec (π : TimePartition T) (t : ℝ≥0) :
    t < π.strictCeilingPoint t ∨ π.strictCeilingPoint t = T := by
  rcases π.strictCeilingIndex_spec t with h | h
  · exact Or.inl h
  · exact Or.inr (by simp only [strictCeilingPoint, h, π.last_eq_horizon])

theorem strictCeilingIndex_le (π : TimePartition T) {t : ℝ≥0} {i : Fin (π.size + 1)}
    (hi : t < π.point i ∨ i = Fin.last π.size) : π.strictCeilingIndex t ≤ i := by
  classical
  apply Finset.min'_le
  simp only [strictUpperIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hi

theorem strictCeilingIndex_mono (π : TimePartition T) : Monotone π.strictCeilingIndex := by
  intro s t hst
  apply π.strictCeilingIndex_le
  exact (π.strictCeilingIndex_spec t).imp (fun h ↦ hst.trans_lt h) id

theorem strictCeilingPoint_mono (π : TimePartition T) : Monotone π.strictCeilingPoint :=
  π.monotone_point.comp π.strictCeilingIndex_mono

theorem le_strictCeilingPoint (π : TimePartition T) {t : ℝ≥0} (ht : t ≤ T) :
    t ≤ π.strictCeilingPoint t := by
  rcases π.strictCeilingPoint_spec t with h | h
  · exact h.le
  · exact ht.trans_eq h.symm

theorem strictCeilingPoint_le_horizon (π : TimePartition T) (t : ℝ≥0) :
    π.strictCeilingPoint t ≤ T := π.point_le_horizon _

theorem strictCeilingPoint_mem (π : TimePartition T) (t : ℝ≥0) :
    π.strictCeilingPoint t ∈ Set.range π.point := ⟨_, rfl⟩

theorem dist_strictCeilingPoint_le_mesh (π : TimePartition T) {t : ℝ≥0} (ht : t ≤ T) :
    dist (π.strictCeilingPoint t) t ≤ (π.mesh : ℝ) := by
  have htc := π.le_strictCeilingPoint ht
  by_cases hzero : π.strictCeilingIndex t = 0
  · have hc : π.strictCeilingPoint t = 0 := by
      simp only [strictCeilingPoint, hzero, π.first_eq_zero]
    have ht0 : t = 0 := le_antisymm (htc.trans_eq hc) bot_le
    rw [hc, ht0, dist_self]
    exact NNReal.coe_nonneg _
  · let i : Fin π.size := (π.strictCeilingIndex t).pred hzero
    have hir : π.right i = π.strictCeilingPoint t := by
      simp [right, i, strictCeilingPoint]
    have hil : π.left i ≤ t := by
      by_contra h
      have hmin := π.strictCeilingIndex_le (i := i.castSucc) (Or.inl (lt_of_not_ge h))
      have hlt : i.castSucc < π.strictCeilingIndex t := by
        simpa [i] using (Fin.castSucc_lt_succ (i := i))
      exact (not_le_of_gt hlt) hmin
    calc
      dist (π.strictCeilingPoint t) t ≤ dist (π.right i) (π.left i) := by
        rw [hir, NNReal.dist_eq, NNReal.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast htc)),
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (hil.trans htc)))]
        exact sub_le_sub_left (by exact_mod_cast hil) _
      _ = (π.gap i : ℝ) := π.dist_right_left_eq_gap i
      _ ≤ π.mesh := by exact_mod_cast π.gap_le_mesh i

theorem strictCeilingPoint_tendsto_nhdsGE_of_eventually_le {U : ℕ → ℝ≥0}
    (π : (n : ℕ) → TimePartition (U n)) (a : ℝ≥0)
    (hU : ∀ᶠ n in atTop, a ≤ U n)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).strictCeilingPoint a) atTop (𝓝[≥] a) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
      (hU.mono fun _ hn ↦ (π _).dist_strictCeilingPoint_le_mesh hn) hmesh
  · filter_upwards [hU] with n hn
    exact (π n).le_strictCeilingPoint hn

end StochLean.TimePartition
