/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.FiniteInsertionLimit
public import StochLean.Probability.Brownian.PartitionDependence

/-! # Nonconvergence along one genuine nested admissible partition sequence

High square sums are obtained by fine dyadics with all old endpoints inserted;
low square sums come from value-midpoint refinement. Each new partition retains
every old endpoint. This is not an interleaving of two unrelated nested sequences.
-/

@[expose] public section

open Set Filter StochLean
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

theorem exists_continuous_nonconvergent_admissible_quadraticVariation :
    ∃ (x : ℝ≥0 → ℝ) (P : ℕ → LocallyFinitePartition), Continuous x ∧
      IsAdmissiblePartitionSequence P ∧
      ¬ ∃ q : ℝ, HasQuadraticVariationAlong (fun n ↦ (P n).restrict 1) x q := by
  classical
  obtain ⟨x, _, hx, _, _, hQ⟩ := exists_continuous_partition_dependent_quadraticVariation
  let D (n : ℕ) := (LocallyFinitePartition.dyadic n).restrict 1
  have hm : Tendsto (fun n ↦ ((D n).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ 1))
  have hs (n : ℕ) (ρ : TimePartition 1) :
      ∃ σ : TimePartition 1, σ.Refines (ρ.commonRefinement (D n)) ∧
        (n % 2 = 0 → quadraticVariationSum σ x < 1 / 4) ∧
        (n % 2 ≠ 0 → 3 / 4 < quadraticVariationSum σ x) := by
    by_cases hn : n % 2 = 0
    · obtain ⟨σ, hσ, _, hq⟩ := (ρ.commonRefinement (D n))
        |>.exists_refinement_quadraticVariationSum_lt hx.continuousOn
          (by norm_num : (0 : ℝ) < 1 / 4)
      exact ⟨σ, hσ, fun _ ↦ hq, fun h ↦ False.elim (h hn)⟩
    · have hl := hasQuadraticVariationAlong_commonRefinement hx.continuousOn hm hQ
        (ρ.commonRefinement (D n))
      obtain ⟨m, hmq⟩ := (hl.eventually_const_lt (by norm_num : (3 / 4 : ℝ) < 1)).exists
      exact ⟨(D m).commonRefinement (ρ.commonRefinement (D n)),
        (D m).commonRefinement_refines_right _, fun h ↦ False.elim (hn h), fun _ ↦ hmq⟩
  choose step hstep using hs
  let ρ : ℕ → TimePartition 1 := Nat.rec (TimePartition.single 1) (fun n π ↦ step n π)
  let π (n : ℕ) := ρ (n + 1)
  have href (n : ℕ) : (π n).Refines ((ρ n).commonRefinement (D n)) := (hstep n (ρ n)).1
  have hn (n : ℕ) : (π (n + 1)).Refines (π n) :=
    fun _ ht ↦ href (n + 1) (((π n).commonRefinement_refines_left (D (n + 1))) ht)
  have hd (n : ℕ) : (π n).Refines (D n) :=
    fun _ ht ↦ href n (((ρ n).commonRefinement_refines_right (D n)) ht)
  have hlo (n : ℕ) : quadraticVariationSum (π (2 * n)) x < 1 / 4 :=
    (hstep (2 * n) (ρ (2 * n))).2.1 (by omega)
  have hhi (n : ℕ) : 3 / 4 < quadraticVariationSum (π (2 * n + 1)) x :=
    (hstep (2 * n + 1) (ρ (2 * n + 1))).2.2 (by omega)
  let P (n : ℕ) := (LocallyFinitePartition.dyadic n).adjoinFinset
    (Finset.univ.image (π n).point)
  have hp : Monotone (fun n ↦ (P n).points) := by
    apply monotone_nat_of_le_succ
    intro n t ht
    rcases ht with ht | ht
    · exact Or.inl (LocallyFinitePartition.dyadic_points_monotone (Nat.le_succ n) ht)
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
      obtain ⟨j, hj⟩ := hn n ⟨i, hi⟩
      exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
  have hmesh : Tendsto (fun n ↦ (P n).mesh) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      LocallyFinitePartition.dyadic_admissible.2 (fun _ ↦ bot_le)
      (fun n ↦ (LocallyFinitePartition.dyadic n).adjoinFinset_mesh_le _)
  have heq (n : ℕ) : quadraticVariationSum ((P n).restrict 1) x = quadraticVariationSum (π n) x :=
    quadraticVariationSum_eq_of_range_eq
      ((LocallyFinitePartition.dyadic n).adjoinFinset_restrict_range (π n) (hd n)) x
  refine ⟨x, P, hx, ⟨hp, hmesh⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hlim := hq.congr heq
  have heven : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    (show StrictMono (fun n : ℕ ↦ 2 * n) from fun _ _ h ↦ by dsimp; omega).tendsto_atTop
  have hodd : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop :=
    (show StrictMono (fun n : ℕ ↦ 2 * n + 1) from fun _ _ h ↦ by dsimp; omega).tendsto_atTop
  have hle : q ≤ 1 / 4 := le_of_tendsto (hlim.comp heven)
    (Eventually.of_forall fun n ↦ (hlo n).le)
  have hge : 3 / 4 ≤ q := ge_of_tendsto (hlim.comp hodd)
    (Eventually.of_forall fun n ↦ (hhi n).le)
  linarith

end ProbabilityTheory
