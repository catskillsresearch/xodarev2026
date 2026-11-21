/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Reflection
public import StochLean.Analysis.PathVariation.Approximation

/-! # Endpoint-set invariance of deterministic sums

An ordered list may repeat its endpoints. Nonempty cells, however, are determined uniquely by
the endpoint set. Thus sums of cell contributions that vanish on empty cells depend only on
the endpoint set, rather than its enumeration.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem exists_cell_right_of_mem (π : TimePartition T) {t : ℝ≥0}
    (ht : t ∈ Set.range π.point) (hpos : 0 < t) :
    ∃ i : Fin π.size, π.left i < t ∧ π.right i = t := by
  obtain ⟨k, hk⟩ := ht
  have htT : t ≤ T := hk ▸ π.point_le_horizon k
  have hcle : π.ceilingPoint t ≤ t := by
    rw [← hk]
    exact π.monotone_point (π.ceilingIndex_le (min_le_left _ _))
  have hceq : π.ceilingPoint t = t :=
    le_antisymm hcle (by simpa only [min_eq_left htT] using π.min_le_ceilingPoint t)
  have hne : π.ceilingIndex t ≠ 0 := by
    intro h
    have hz : π.ceilingPoint t = 0 := by simp [ceilingPoint, h, π.first_eq_zero]
    exact (ne_of_gt hpos) (hceq.symm.trans hz)
  let i : Fin π.size := (π.ceilingIndex t).pred hne
  refine ⟨i, ?_, ?_⟩
  · apply lt_of_not_ge
    intro hle
    have hmin := π.ceilingIndex_le (i := i.castSucc) ((min_le_left t T).trans hle)
    have hlt : i.castSucc < π.ceilingIndex t := by
      simpa [i] using (Fin.castSucc_lt_succ (i := i))
    exact (not_le_of_gt hlt) hmin
  · simpa [right, i, ceilingPoint] using hceq

theorem exists_matching_cell_of_range_eq {π ρ : TimePartition T}
    (heq : Set.range π.point = Set.range ρ.point) {i : Fin π.size}
    (hi : π.left i < π.right i) :
    ∃ j : Fin ρ.size, ρ.left j = π.left i ∧ ρ.right j = π.right i := by
  have hmem : π.right i ∈ Set.range ρ.point := heq ▸ (show π.right i ∈ Set.range π.point
    from ⟨i.succ, rfl⟩)
  obtain ⟨j, hj, hr⟩ := ρ.exists_cell_right_of_mem hmem ((bot_le : 0 ≤ π.left i).trans_lt hi)
  refine ⟨j, le_antisymm ?_ ?_, hr⟩
  · have hmem' : ρ.left j ∈ Set.range π.point := heq.symm ▸
      (show ρ.left j ∈ Set.range ρ.point from ⟨j.castSucc, rfl⟩)
    rcases π.endpoint_le_left_or_right_le hmem' i with h | h
    · exact h
    · exact False.elim ((not_le_of_gt hj) h)
  · have hmem' : π.left i ∈ Set.range ρ.point := heq ▸
      (show π.left i ∈ Set.range π.point from ⟨i.castSucc, rfl⟩)
    rcases ρ.endpoint_le_left_or_right_le hmem' j with h | h
    · exact h
    · exact False.elim ((not_le_of_gt hi) (hr ▸ h))

theorem eq_of_nonempty_cell_endpoints (π : TimePartition T) {i j : Fin π.size}
    (hi : π.left i < π.right i) (hl : π.left i = π.left j)
    (hr : π.right i = π.right j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have h : π.right i ≤ π.left j := π.monotone_point (show i.succ ≤ j.castSucc from hij)
    exact False.elim ((not_le_of_gt hi) (hl ▸ h))
  · exact hij
  · have h : π.right j ≤ π.left i := π.monotone_point (show j.succ ≤ i.castSucc from hji)
    exact False.elim ((not_le_of_gt hi) (hr ▸ h))

theorem sum_nonempty_cells {E : Type*} [AddCommMonoid E] (π : TimePartition T)
    (F : ℝ≥0 → ℝ≥0 → E) (hF : ∀ t, F t t = 0) :
    (∑ i ∈ univ.filter (fun i ↦ π.left i < π.right i), F (π.left i) (π.right i)) =
      ∑ i, F (π.left i) (π.right i) := by
  classical
  apply sum_subset (filter_subset _ _)
  intro i _ hi
  have hle : π.right i ≤ π.left i := by simpa only [mem_filter, Finset.mem_univ, true_and,
    not_lt] using hi
  rw [le_antisymm (π.left_le_right i) hle, hF]

/-- Inserting or removing repeated endpoints does not change any cell sum whose diagonal
contribution is zero. This is not a refinement-invariance assertion. -/
theorem sum_cells_eq_of_range_eq {E : Type*} [AddCommMonoid E]
    {π ρ : TimePartition T} (heq : Set.range π.point = Set.range ρ.point)
    (F : ℝ≥0 → ℝ≥0 → E) (hF : ∀ t, F t t = 0) :
    (∑ i, F (π.left i) (π.right i)) = ∑ j, F (ρ.left j) (ρ.right j) := by
  classical
  rw [← π.sum_nonempty_cells F hF, ← ρ.sum_nonempty_cells F hF]
  let A := univ.filter (fun i ↦ π.left i < π.right i)
  let C := univ.filter (fun j ↦ ρ.left j < ρ.right j)
  have hm (i : Fin π.size) (hi : i ∈ A) :
      ∃ j : Fin ρ.size, j ∈ C ∧ ρ.left j = π.left i ∧ ρ.right j = π.right i := by
    have hi' := (mem_filter.mp hi).2
    obtain ⟨j, hl, hr⟩ := exists_matching_cell_of_range_eq heq hi'
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, by simpa only [hl, hr] using hi'⟩, hl, hr⟩
  choose e he using hm
  apply sum_bij e (fun i hi ↦ (he i hi).1)
  · intro i hi j hj hij
    apply π.eq_of_nonempty_cell_endpoints (mem_filter.mp hi).2
    · exact (he i hi).2.1.symm.trans ((congrArg ρ.left hij).trans (he j hj).2.1)
    · exact (he i hi).2.2.symm.trans ((congrArg ρ.right hij).trans (he j hj).2.2)
  · intro j hj
    obtain ⟨i, hl, hr⟩ := exists_matching_cell_of_range_eq heq.symm (mem_filter.mp hj).2
    have hi : i ∈ A := mem_filter.mpr ⟨mem_univ _, by
      simpa only [hl, hr] using (mem_filter.mp hj).2⟩
    refine ⟨i, hi, ?_⟩
    exact ρ.eq_of_nonempty_cell_endpoints (mem_filter.mp (he i hi).1).2
      ((he i hi).2.1.trans hl) ((he i hi).2.2.trans hr)
  · intro i hi
    exact congrArg₂ F (he i hi).2.1.symm (he i hi).2.2.symm

end StochLean.TimePartition

namespace StochLean

theorem quadraticVariationSum_eq_of_range_eq {T : ℝ≥0} {π ρ : TimePartition T}
    (heq : Set.range π.point = Set.range ρ.point) (f : ℝ≥0 → ℝ) :
    quadraticVariationSum π f = quadraticVariationSum ρ f :=
  TimePartition.sum_cells_eq_of_range_eq heq (fun a b ↦ (f b - f a) ^ 2) (by simp)

theorem covariationSum_eq_of_range_eq {T : ℝ≥0} {π ρ : TimePartition T}
    (heq : Set.range π.point = Set.range ρ.point) (f g : ℝ≥0 → ℝ) :
    covariationSum π f g = covariationSum ρ f g :=
  TimePartition.sum_cells_eq_of_range_eq heq (fun a b ↦ (f b - f a) * (g b - g a)) (by simp)

end StochLean
