/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.UniformPartition
public import StochLean.Analysis.PathVariation.Approximation

/-! # Existing dyadic partitions on expanding integer horizons

The grid at stage n is the existing dyadic partition restricted to [0,n].
Every integer belongs to every dyadic grid, so these finite endpoint sets
increase even when the horizon grows. Their ceiling projections approach
each fixed time from the right, which transports right-continuous path values.
-/

@[expose] public section

open Filter Set
open scoped NNReal ENNReal Topology

namespace StochLean

theorem LocallyFinitePartition.natCast_mem_dyadic (n k : ℕ) :
    (k : ℝ≥0) ∈ (dyadic n).points := by
  apply dyadic_points_monotone (Nat.zero_le n)
  refine ⟨k, ?_⟩
  change (k : ℝ≥0) * (1 / 2 : ℝ≥0) ^ 0 = (k : ℝ≥0)
  simp

/-- Reuse of the canonical dyadic grid, with growing finite horizons. -/
noncomputable def TimePartition.expandingDyadic (n : ℕ) : TimePartition (n : ℝ≥0) :=
  (LocallyFinitePartition.dyadic n).restrict (n : ℝ≥0)

theorem TimePartition.expandingDyadic_range_mono :
    Monotone (fun n ↦ Set.range (expandingDyadic n).point) := by
  intro i j hij t ht
  change t ∈ Set.range ((LocallyFinitePartition.dyadic i).restrict (i : ℝ≥0)).point at ht
  change t ∈ Set.range ((LocallyFinitePartition.dyadic j).restrict (j : ℝ≥0)).point
  rw [LocallyFinitePartition.mem_range_restrict] at ht ⊢
  rcases ht with rfl | ⟨ht, hti⟩
  · exact Or.inr ⟨LocallyFinitePartition.natCast_mem_dyadic j i, by exact_mod_cast hij⟩
  · exact Or.inr ⟨LocallyFinitePartition.dyadic_points_monotone hij ht,
      hti.trans (by exact_mod_cast hij)⟩

theorem TimePartition.expandingDyadic_mesh_le (n : ℕ) :
    (expandingDyadic n).mesh ≤ (1 / 2 : ℝ≥0) ^ n := by
  apply ENNReal.coe_le_coe.mp
  exact ((LocallyFinitePartition.dyadic n).restrict_mesh_le (n : ℝ≥0)).trans
    (LocallyFinitePartition.uniform_mesh_le _ _)

theorem TimePartition.expandingDyadic_le_ceilingPoint_eventually (t : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, t ≤ (expandingDyadic n).ceilingPoint t := by
  obtain ⟨N, hN⟩ := exists_nat_ge t
  filter_upwards [eventually_ge_atTop N] with n hn
  have ht : t ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast hn)
  simpa only [min_eq_left ht] using (expandingDyadic n).min_le_ceilingPoint t

theorem TimePartition.expandingDyadic_ceilingPoint_tendsto (t : ℝ≥0) :
    Tendsto (fun n ↦ (expandingDyadic n).ceilingPoint t) atTop (𝓝 t) := by
  have hpow : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_ge t
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ hpow
  filter_upwards [eventually_ge_atTop N] with n hn
  have ht : t ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast hn)
  apply ((expandingDyadic n).dist_ceilingPoint_le_mesh ht).trans
  exact_mod_cast expandingDyadic_mesh_le n

theorem TimePartition.tendsto_eval_expandingDyadic_ceilingPoint
    {E : Type*} [TopologicalSpace E] {f : ℝ≥0 → E} {t : ℝ≥0}
    (hr : ContinuousWithinAt f (Ici t) t) :
    Tendsto (fun n ↦ f ((expandingDyadic n).ceilingPoint t)) atTop (𝓝 (f t)) :=
  hr.tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨expandingDyadic_ceilingPoint_tendsto t, expandingDyadic_le_ceilingPoint_eventually t⟩)

end StochLean
