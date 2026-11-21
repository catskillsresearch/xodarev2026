/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.MidpointRefinement
public import StochLean.Analysis.PathVariation.CommonRefinement
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # Nested vanishing-mesh partitions with zero square-sum limit

The partitions are chosen from the particular continuous path. This does not
assert that any fixed partition sequence gives zero quadratic variation.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace StochLean

theorem exists_nested_zeroQuadraticVariation_partitions {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) :
    ∃ π : ℕ → TimePartition T,
      (∀ n, (π (n + 1)).Refines (π n)) ∧
      (∀ n, (π n).Refines ((LocallyFinitePartition.dyadic n).restrict T)) ∧
      Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) ∧ HasQuadraticVariationAlong π x 0 := by
  let D (n : ℕ) := (LocallyFinitePartition.dyadic n).restrict T
  have hs (n : ℕ) (ρ : TimePartition T) :
      ∃ σ : TimePartition T, σ.Refines (ρ.commonRefinement (D n)) ∧
        σ.mesh ≤ (ρ.commonRefinement (D n)).mesh ∧ quadraticVariationSum σ x < (1 / 2 : ℝ) ^ n :=
    (ρ.commonRefinement (D n)).exists_refinement_quadraticVariationSum_lt hx
      (pow_pos (by norm_num) n)
  choose step hstep using hs
  let π : ℕ → TimePartition T := Nat.rec (TimePartition.single T) (fun n ρ ↦ step n ρ)
  have href (n : ℕ) : (π (n + 1)).Refines ((π n).commonRefinement (D n)) :=
    (hstep n (π n)).1
  have hd (n : ℕ) : (π (n + 1)).Refines (D n) :=
    fun _ ht ↦ href n (((π n).commonRefinement_refines_right (D n)) ht)
  have hmesh (n : ℕ) : (π (n + 1)).mesh ≤ (D n).mesh := (hd n).mesh_le
  have hq (n : ℕ) : quadraticVariationSum (π (n + 1)) x < (1 / 2 : ℝ) ^ n :=
    (hstep n (π n)).2.2
  refine ⟨fun n ↦ π (n + 1), ?_, hd, ?_, ?_⟩
  · intro n t ht
    exact href (n + 1) (((π (n + 1)).commonRefinement_refines_left (D (n + 1))) ht)
  · have hm : Tendsto (fun n ↦ ((D n).mesh : ℝ)) atTop (𝓝 0) := by
      exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
        (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ T))
    exact squeeze_zero (fun _ ↦ NNReal.coe_nonneg _) (fun n ↦ by exact_mod_cast hmesh n) hm
  · exact squeeze_zero (fun n ↦ quadraticVariationSum_nonneg (π (n + 1)) x)
      (fun n ↦ (hq n).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))

end StochLean
