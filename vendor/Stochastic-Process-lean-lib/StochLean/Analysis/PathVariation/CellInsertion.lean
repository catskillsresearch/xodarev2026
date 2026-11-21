/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.MidpointRefinement

/-! # Exact square-sum error from inserting a point in one cell

The interlaced partition construction is reused. In other cells the inserted
point is just the old left endpoint, so its additional increment is zero.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem midpointRefinement_range (π : TimePartition T) (u : Fin π.size → ℝ≥0)
    (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) :
    Set.range (π.midpointRefinement u hu).point = Set.range π.point ∪ Set.range u := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i.val < π.size * 2 + 1 := i.isLt
    change (if h : i.val % 2 = 0 then π.point ⟨i.val / 2, by omega⟩
      else u ⟨i.val / 2, by omega⟩) ∈ _
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · rintro (ht | ⟨i, rfl⟩)
    · exact π.midpointRefinement_refines u hu ht
    · exact ⟨_, π.midpointRefinement_point_odd u hu i⟩

theorem midpointRefinement_increment_even (π : TimePartition T) (u : Fin π.size → ℝ≥0)
    (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) (x : ℝ≥0 → ℝ) (i : Fin π.size) :
    (π.midpointRefinement u hu).increment x (finProdFinEquiv (i, (0 : Fin 2))) =
      x (u i) - x (π.left i) := by
  have hl := π.midpointRefinement_point_even u hu i.castSucc
  have hr := π.midpointRefinement_point_odd u hu i
  change x ((π.midpointRefinement u hu).point _) -
    x ((π.midpointRefinement u hu).point _) = _
  congr 1
  · convert congrArg x hr using 1
    congr 2
    apply Fin.ext
    simp [finProdFinEquiv, Fin.succ]
  · convert congrArg x hl using 1 <;> congr 2
    apply Fin.ext
    simp [finProdFinEquiv, Fin.castSucc, Fin.castAdd, Fin.castLE]

theorem midpointRefinement_increment_odd (π : TimePartition T) (u : Fin π.size → ℝ≥0)
    (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) (x : ℝ≥0 → ℝ) (i : Fin π.size) :
    (π.midpointRefinement u hu).increment x (finProdFinEquiv (i, (1 : Fin 2))) =
      x (π.right i) - x (u i) := by
  have hl := π.midpointRefinement_point_odd u hu i
  have hr := π.midpointRefinement_point_even u hu i.succ
  change x ((π.midpointRefinement u hu).point _) -
    x ((π.midpointRefinement u hu).point _) = _
  congr 1
  · convert congrArg x hr using 1 <;> congr 2
    apply Fin.ext
    simp [finProdFinEquiv, Fin.succ]
    omega
  · convert congrArg x hl using 1
    congr 2
    apply Fin.ext
    simp [finProdFinEquiv, Fin.castSucc, Fin.castAdd, Fin.castLE]
    omega

theorem quadraticVariationSum_midpointRefinement_expansion (π : TimePartition T)
    (u : Fin π.size → ℝ≥0) (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) (x : ℝ≥0 → ℝ) :
    quadraticVariationSum (π.midpointRefinement u hu) x =
      ∑ i : Fin π.size, ((x (u i) - x (π.left i)) ^ 2 + (x (π.right i) - x (u i)) ^ 2) := by
  change (∑ j : Fin (π.size * 2), ((π.midpointRefinement u hu).increment x j) ^ 2) = _
  rw [← (finProdFinEquiv : Fin π.size × Fin 2 ≃ Fin (π.size * 2)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, midpointRefinement_increment_even, midpointRefinement_increment_odd]

theorem exists_insertPoint_in_cell (π : TimePartition T) (i : Fin π.size)
    {s : ℝ≥0} (hs : π.left i ≤ s ∧ s ≤ π.right i) (x : ℝ≥0 → ℝ) :
    ∃ ρ : TimePartition T, ρ.Refines π ∧
      Set.range ρ.point = insert s (Set.range π.point) ∧
      quadraticVariationSum ρ x = quadraticVariationSum π x -
        2 * (x s - x (π.left i)) * (x (π.right i) - x s) := by
  classical
  let u (j : Fin π.size) := if j = i then s else π.left j
  have hu (j : Fin π.size) : π.left j ≤ u j ∧ u j ≤ π.right j := by
    by_cases hj : j = i
    · simpa only [u, hj, ↓reduceIte] using hs
    · simp only [u, hj, ↓reduceIte, le_refl, π.left_le_right, and_self]
  refine ⟨π.midpointRefinement u hu, π.midpointRefinement_refines u hu, ?_, ?_⟩
  · rw [midpointRefinement_range]
    ext t
    constructor
    · rintro (ht | ⟨j, rfl⟩)
      · exact Or.inr ht
      · by_cases hj : j = i
        · exact Or.inl (by simp only [u, hj, ↓reduceIte])
        · exact Or.inr ⟨j.castSucc, by simp only [u, hj, ↓reduceIte, left]⟩
    · rintro (rfl | ht)
      · exact Or.inr ⟨i, by simp only [u, ↓reduceIte]⟩
      · exact Or.inl ht
  · rw [quadraticVariationSum_midpointRefinement_expansion]
    have he : (∑ j : Fin π.size,
        2 * (x (u j) - x (π.left j)) * (x (π.right j) - x (u j))) =
          2 * (x s - x (π.left i)) * (x (π.right i) - x s) := by
      rw [sum_eq_single i]
      · simp only [u, ↓reduceIte]
      · intro j _ hji
        simp only [u, hji, ↓reduceIte, sub_self, mul_zero, zero_mul]
      · simp
    rw [← he, quadraticVariationSum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    dsimp only [increment]
    ring

end StochLean.TimePartition
