/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.AdmissiblePartition
public import StochLean.Analysis.PathVariation.Reflection
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform infinite partitions and a concrete admissible dyadic sequence

These are actual locally finite, unbounded endpoint sets. The maximum adjacent-gap bound is
proved for every finite restriction, including the final partial cell and horizon zero.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal ENNReal Topology

namespace StochLean.LocallyFinitePartition

def uniform (δ : ℝ≥0) (hδ : 0 < δ) : LocallyFinitePartition where
  points := Set.range (fun k : ℕ ↦ (k : ℝ≥0) * δ)
  zero_mem := ⟨0, by simp⟩
  finite_bounded T := by
    obtain ⟨N, hN⟩ := exists_nat_ge (T / δ)
    apply (((Finset.range (N + 1)).finite_toSet).image (fun k : ℕ ↦ (k : ℝ≥0) * δ)).subset
    rintro t ⟨⟨k, rfl⟩, _, ht⟩
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_range]
    apply Nat.lt_succ_of_le
    exact_mod_cast (((le_div_iff₀ hδ).mpr ht).trans hN)
  unbounded := by
    rintro ⟨M, hM⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (M / δ)
    have hlt : M < (k : ℝ≥0) * δ := (div_lt_iff₀ hδ).mp hk
    exact (not_le_of_gt hlt) (hM ⟨k, rfl⟩)

theorem uniform_restrict_gap_le (δ : ℝ≥0) (hδ : 0 < δ) (T : ℝ≥0)
    (i : Fin ((uniform δ hδ).restrict T).size) :
    ((uniform δ hδ).restrict T).gap i ≤ δ := by
  let ρ := (uniform δ hδ).restrict T
  have hleft : ρ.left i = T ∨ ρ.left i ∈ (uniform δ hδ).points ∧ ρ.left i ≤ T :=
    ((uniform δ hδ).mem_range_restrict T _).mp ⟨i.castSucc, rfl⟩
  rcases hleft with hleft | ⟨⟨k, hk⟩, _⟩
  · change ρ.right i - ρ.left i ≤ δ
    have hr : ρ.right i ≤ ρ.left i := (ρ.point_le_horizon i.succ).trans_eq hleft.symm
    rw [tsub_eq_zero_of_le hr]
    exact bot_le
  · have hnext : ρ.left i + δ ∈ (uniform δ hδ).points := by
      refine ⟨k + 1, ?_⟩
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hk]
    have hright : ρ.right i ≤ ρ.left i + δ := by
      by_cases hT : ρ.left i + δ ≤ T
      · have hmem := ((uniform δ hδ).mem_range_restrict T _).mpr (Or.inr ⟨hnext, hT⟩)
        rcases ρ.endpoint_le_left_or_right_le hmem i with h | h
        · exact False.elim ((not_le_of_gt (lt_add_of_pos_right (ρ.left i) hδ)) h)
        · exact h
      · exact (ρ.point_le_horizon i.succ).trans (le_of_not_ge hT)
    change ρ.right i - ρ.left i ≤ δ
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hright)

theorem uniform_mesh_le (δ : ℝ≥0) (hδ : 0 < δ) : (uniform δ hδ).mesh ≤ (δ : ℝ≥0∞) := by
  apply iSup_le
  intro T
  apply ENNReal.coe_le_coe.mpr
  exact Finset.sup_le (fun i _ ↦ uniform_restrict_gap_le δ hδ T i)

noncomputable def dyadic (n : ℕ) : LocallyFinitePartition :=
  uniform ((1 / 2 : ℝ≥0) ^ n) (pow_pos (by norm_num) n)

theorem dyadic_points_monotone : Monotone (fun n ↦ (dyadic n).points) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨2 * k, ?_⟩
  change ((2 * k : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ (n + 1) = x
  rw [← hk]
  push_cast
  rw [pow_succ]
  ring

theorem dyadic_admissible : IsAdmissiblePartitionSequence dyadic := by
  refine ⟨dyadic_points_monotone, ?_⟩
  have hlim : Tendsto (fun n ↦ (((1 / 2 : ℝ≥0) ^ n) : ℝ≥0∞)) atTop (𝓝 0) :=
    ENNReal.tendsto_coe.mpr (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) (fun n ↦ uniform_mesh_le _ _)

end StochLean.LocallyFinitePartition
