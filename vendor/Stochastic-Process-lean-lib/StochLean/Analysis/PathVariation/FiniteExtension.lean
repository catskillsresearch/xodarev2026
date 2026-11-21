/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.SmallVariationPartitions
public import StochLean.Analysis.PathVariation.EndpointInvariance

/-! # Extending finite refinements to genuine admissible infinite partitions

Adjoining finitely many endpoints preserves local finiteness and cannot increase
the global adjacent-gap mesh. This realizes the path-dependent zero-QV sequence
inside the same infinite-partition owner used by Klenke admissibility.
-/

@[expose] public section

open Set Finset Filter
open scoped NNReal ENNReal Topology

namespace StochLean
namespace LocallyFinitePartition

def adjoinFinset (P : LocallyFinitePartition) (s : Finset ℝ≥0) : LocallyFinitePartition where
  points := P.points ∪ (s : Set ℝ≥0)
  zero_mem := Or.inl P.zero_mem
  finite_bounded T := by
    rw [union_inter_distrib_right]
    exact (P.finite_bounded T).union (s.finite_toSet.inter_of_left _)
  unbounded h := P.unbounded (h.mono subset_union_left)

theorem adjoinFinset_mesh_le (P : LocallyFinitePartition) (s : Finset ℝ≥0) :
    (P.adjoinFinset s).mesh ≤ P.mesh := by
  apply iSup_le
  intro T
  have hr : ((P.adjoinFinset s).restrict T).Refines (P.restrict T) := by
    intro t ht
    rcases (P.mem_range_restrict T t).mp ht with ht | ⟨ht, htT⟩
    · exact ((P.adjoinFinset s).mem_range_restrict T t).mpr (Or.inl ht)
    · exact ((P.adjoinFinset s).mem_range_restrict T t).mpr (Or.inr ⟨Or.inl ht, htT⟩)
  exact (ENNReal.coe_le_coe.mpr hr.mesh_le).trans (P.restrict_mesh_le T)

theorem adjoinFinset_restrict_range {T : ℝ≥0} (P : LocallyFinitePartition)
    (π : TimePartition T) (hπ : π.Refines (P.restrict T)) :
    Set.range ((P.adjoinFinset (univ.image π.point)).restrict T).point = Set.range π.point := by
  classical
  ext t
  rw [mem_range_restrict]
  constructor
  · rintro (ht | ⟨ht, htT⟩)
    · exact ⟨Fin.last π.size, π.last_eq_horizon.trans ht.symm⟩
    · rcases ht with ht | ht
      · exact hπ ((P.mem_range_restrict T t).mpr (Or.inr ⟨ht, htT⟩))
      · obtain ⟨i, _, hi⟩ := mem_image.mp ht
        exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact Or.inr ⟨Or.inr (mem_image.mpr ⟨i, mem_univ _, rfl⟩), π.point_le_horizon i⟩

end LocallyFinitePartition

theorem exists_admissible_zeroQuadraticVariation {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) :
    ∃ P : ℕ → LocallyFinitePartition, IsAdmissiblePartitionSequence P ∧
      HasQuadraticVariationAlong (fun n ↦ (P n).restrict T) x 0 := by
  classical
  obtain ⟨π, hn, hd, _, hq⟩ := exists_nested_zeroQuadraticVariation_partitions hx
  let P (n : ℕ) := (LocallyFinitePartition.dyadic n).adjoinFinset (univ.image (π n).point)
  have hm : Monotone (fun n ↦ (P n).points) := by
    apply monotone_nat_of_le_succ
    intro n t ht
    rcases ht with ht | ht
    · exact Or.inl (LocallyFinitePartition.dyadic_points_monotone (Nat.le_succ n) ht)
    · obtain ⟨i, _, hi⟩ := mem_image.mp ht
      obtain ⟨j, hj⟩ := hn n ⟨i, hi⟩
      exact Or.inr (mem_image.mpr ⟨j, mem_univ _, hj⟩)
  have hmesh : Tendsto (fun n ↦ (P n).mesh) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      LocallyFinitePartition.dyadic_admissible.2 (fun _ ↦ bot_le)
      (fun n ↦ (LocallyFinitePartition.dyadic n).adjoinFinset_mesh_le _)
  refine ⟨P, ⟨hm, hmesh⟩, ?_⟩
  exact hq.congr (fun n ↦ (quadraticVariationSum_eq_of_range_eq
    ((LocallyFinitePartition.dyadic n).adjoinFinset_restrict_range (π n) (hd n)) x).symm)

end StochLean
