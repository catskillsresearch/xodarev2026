/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.AdmissiblePartition
public import StochLean.Analysis.PathVariation.TotalVariation

/-! # A finite common refinement by the union of actual endpoints -/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

noncomputable def commonRefinement (π ρ : TimePartition T) : TimePartition T :=
  ofFinset (univ.image π.point ∪ univ.image ρ.point)
    (mem_union_left _ (mem_image.mpr ⟨0, mem_univ _, π.first_eq_zero⟩))
    (mem_union_left _ (mem_image.mpr ⟨Fin.last π.size, mem_univ _, π.last_eq_horizon⟩))
    (by
      intro t ht
      rcases mem_union.mp ht with ht | ht
      · obtain ⟨i, _, rfl⟩ := mem_image.mp ht
        exact π.point_le_horizon i
      · obtain ⟨i, _, rfl⟩ := mem_image.mp ht
        exact ρ.point_le_horizon i)

theorem commonRefinement_range (π ρ : TimePartition T) :
    Set.range (π.commonRefinement ρ).point = Set.range π.point ∪ Set.range ρ.point := by
  rw [commonRefinement, ofFinset_range]
  simp

theorem commonRefinement_refines_left (π ρ : TimePartition T) :
    (π.commonRefinement ρ).Refines π := by
  intro t ht
  rw [commonRefinement_range]
  exact Or.inl ht

theorem commonRefinement_refines_right (π ρ : TimePartition T) :
    (π.commonRefinement ρ).Refines ρ := by
  intro t ht
  rw [commonRefinement_range]
  exact Or.inr ht

end StochLean.TimePartition
