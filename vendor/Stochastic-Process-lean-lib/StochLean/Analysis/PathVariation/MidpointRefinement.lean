/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TotalVariation
public import StochLean.Analysis.PathVariation.LeftStepApproximation
public import StochLean.Analysis.PathVariation.Reflection
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Refining a continuous path at intermediate values

One point in each old cell is inserted without deleting old endpoints.
Choosing the midpoint of the endpoint *values* halves the square sum; this
is different from bisecting the time interval. Empty cells remain legal.
-/

@[expose] public section

open Set Finset Filter
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem Refines.mesh_le {π ρ : TimePartition T} (h : π.Refines ρ) : π.mesh ≤ ρ.mesh := by
  apply Finset.sup_le
  intro i _
  by_cases hz : π.right i = 0
  · have hl : π.left i = 0 := le_antisymm ((π.left_le_right i).trans_eq hz) bot_le
    simp only [gap, hl, hz, tsub_self, zero_le]
  · obtain ⟨j, hj⟩ := ρ.exists_cell ⟨pos_iff_ne_zero.mpr hz, π.point_le_horizon _⟩
    have hl : ρ.left j ≤ π.left i := by
      rcases π.endpoint_le_left_or_right_le (h ⟨j.castSucc, rfl⟩) i with hl | hl
      · exact hl
      · exact False.elim ((not_le_of_gt hj.1) hl)
    exact (tsub_le_tsub hj.2 hl).trans (ρ.gap_le_mesh j)

def midpointRefinement (π : TimePartition T) (u : Fin π.size → ℝ≥0)
    (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) : TimePartition T where
  size := π.size * 2
  point i := if h : i.val % 2 = 0 then π.point ⟨i.val / 2, by omega⟩
    else u ⟨i.val / 2, by omega⟩
  monotone_point := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hi := i.isLt
    by_cases he : i.val % 2 = 0
    · have ho : (i.val + 1) % 2 ≠ 0 := by omega
      have hd : (i.val + 1) / 2 = i.val / 2 := by omega
      simp only [Fin.val_castSucc, Fin.val_succ, he, ho, ↓reduceDIte]
      convert (hu ⟨i.val / 2, by omega⟩).1 using 1 <;> congr 1
      apply Fin.ext
      simp only [hd]
    · have ho : (i.val + 1) % 2 = 0 := by omega
      have hd : (i.val + 1) / 2 = i.val / 2 + 1 := by omega
      simp only [Fin.val_castSucc, Fin.val_succ, he, ho, ↓reduceDIte]
      convert (hu ⟨i.val / 2, by omega⟩).2 using 1
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ, hd]
  first_eq_zero := by simpa using π.first_eq_zero
  last_eq_horizon := by simpa [Fin.last] using π.last_eq_horizon

theorem midpointRefinement_point_even (π : TimePartition T) (u : Fin π.size → ℝ≥0)
    (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) (i : Fin (π.size + 1)) :
    (π.midpointRefinement u hu).point
      ⟨2 * i.val, by have := i.isLt; dsimp [midpointRefinement]; omega⟩ = π.point i := by
  simp [midpointRefinement, Nat.mul_comm]

theorem midpointRefinement_point_odd (π : TimePartition T) (u : Fin π.size → ℝ≥0)
    (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) (i : Fin π.size) :
    (π.midpointRefinement u hu).point
      ⟨2 * i.val + 1, by have := i.isLt; dsimp [midpointRefinement]; omega⟩ = u i := by
  simp [midpointRefinement, Nat.mul_comm, Nat.add_div]

theorem midpointRefinement_refines (π : TimePartition T) (u : Fin π.size → ℝ≥0)
    (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i) : (π.midpointRefinement u hu).Refines π := by
  rintro t ⟨i, rfl⟩
  exact ⟨_, π.midpointRefinement_point_even u hu i⟩

theorem quadraticVariationSum_midpointRefinement (π : TimePartition T)
    (u : Fin π.size → ℝ≥0) (hu : ∀ i, π.left i ≤ u i ∧ u i ≤ π.right i)
    (x : ℝ≥0 → ℝ) (hx : ∀ i, x (u i) = (x (π.left i) + x (π.right i)) / 2) :
    quadraticVariationSum (π.midpointRefinement u hu) x = quadraticVariationSum π x / 2 := by
  let ρ := π.midpointRefinement u hu
  have he (i : Fin π.size) :
      ρ.increment x (finProdFinEquiv (i, (0 : Fin 2))) = (π.increment x i) / 2 := by
    have hl := π.midpointRefinement_point_even u hu i.castSucc
    have hr := π.midpointRefinement_point_odd u hu i
    change x (ρ.point _) - x (ρ.point _) = _
    convert_to x (u i) - x (π.left i) = (π.increment x i) / 2
    · congr 1
      · convert congrArg x hr using 1
        congr 2
        apply Fin.ext
        simp [finProdFinEquiv, Fin.succ]
      · convert congrArg x hl using 1 <;> congr 2
        apply Fin.ext
        simp [finProdFinEquiv, Fin.castSucc, Fin.castAdd, Fin.castLE]
    rw [hx, increment]
    ring
  have ho (i : Fin π.size) :
      ρ.increment x (finProdFinEquiv (i, (1 : Fin 2))) = (π.increment x i) / 2 := by
    have hl := π.midpointRefinement_point_odd u hu i
    have hr := π.midpointRefinement_point_even u hu i.succ
    change x (ρ.point _) - x (ρ.point _) = _
    convert_to x (π.right i) - x (u i) = (π.increment x i) / 2
    · congr 1
      · convert congrArg x hr using 1 <;> congr 2
        apply Fin.ext
        simp [finProdFinEquiv, Fin.succ]
        omega
      · convert congrArg x hl using 1
        congr 2
        apply Fin.ext
        simp [finProdFinEquiv, Fin.castSucc, Fin.castAdd, Fin.castLE]
        omega
    rw [hx, increment]
    ring
  change (∑ j : Fin (π.size * 2), (ρ.increment x j) ^ 2) = _
  rw [← (finProdFinEquiv : Fin π.size × Fin 2 ≃ Fin (π.size * 2)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two, he, ho]
  rw [quadraticVariationSum, div_eq_mul_inv, Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  ring

theorem exists_midpointRefinement (π : TimePartition T) {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) :
    ∃ ρ : TimePartition T, ρ.Refines π ∧
      quadraticVariationSum ρ x = quadraticVariationSum π x / 2 := by
  have hi (i : Fin π.size) :
      ∃ u ∈ Icc (π.left i) (π.right i), x u = (x (π.left i) + x (π.right i)) / 2 := by
    have hc : ContinuousOn x (uIcc (π.left i) (π.right i)) := by
      rw [uIcc_of_le (π.left_le_right i)]
      exact hx.mono (Icc_subset_Icc bot_le (π.point_le_horizon _))
    have hm : (x (π.left i) + x (π.right i)) / 2 ∈ uIcc (x (π.left i)) (x (π.right i)) := by
      rcases le_total (x (π.left i)) (x (π.right i)) with h | h
      · rw [uIcc_of_le h]; constructor <;> linarith
      · rw [uIcc_of_ge h]; constructor <;> linarith
    obtain ⟨u, hu, he⟩ := intermediate_value_uIcc hc hm
    exact ⟨u, by simpa only [uIcc_of_le (π.left_le_right i)] using hu, he⟩
  choose u hu he using hi
  exact ⟨π.midpointRefinement u hu, π.midpointRefinement_refines u hu,
    quadraticVariationSum_midpointRefinement π u hu x he⟩

theorem exists_iterated_midpointRefinement (π : TimePartition T) {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) (n : ℕ) :
    ∃ ρ : TimePartition T, ρ.Refines π ∧
      quadraticVariationSum ρ x = (1 / 2 : ℝ) ^ n * quadraticVariationSum π x := by
  induction n with
  | zero => exact ⟨π, fun _ h ↦ h, by simp⟩
  | succ n ih =>
    obtain ⟨ρ, hρ, heρ⟩ := ih
    obtain ⟨σ, hσ, heσ⟩ := ρ.exists_midpointRefinement hx
    refine ⟨σ, fun _ h ↦ hσ (hρ h), ?_⟩
    rw [heσ, heρ, pow_succ]
    ring

/-- Any prescribed finite partition has a refinement with arbitrarily small
square sum, even when the path has infinite total variation. -/
theorem exists_refinement_quadraticVariationSum_lt (π : TimePartition T)
    {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : TimePartition T, ρ.Refines π ∧ ρ.mesh ≤ π.mesh ∧ quadraticVariationSum ρ x < ε := by
  have hlim : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * quadraticVariationSum π x)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (quadraticVariationSum π x)
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  obtain ⟨ρ, hρ, he⟩ := π.exists_iterated_midpointRefinement hx n
  exact ⟨ρ, hρ, hρ.mesh_le, he.trans_lt hn⟩

end StochLean.TimePartition
