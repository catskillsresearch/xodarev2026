/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.QuadraticPairSums

/-! # Quadratic-pair estimates after removing finitely selected cells -/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

theorem quadraticPairSum_terminal {T : ℝ≥0} (π : TimePartition T)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) :
    quadraticPairSum π Φ x T =
      ∑ i : Fin π.size, Φ (x (π.left i)) (x (π.right i)) * (π.increment x i) ^ 2 := by
  apply sum_congr rfl
  intro i _
  rw [min_eq_left (show π.left i ≤ T from π.point_le_horizon i.castSucc),
    min_eq_left (show π.right i ≤ T from π.point_le_horizon i.succ)]
  rfl

theorem norm_quadraticPairSum_sub_selected_le {T : ℝ≥0} (π : TimePartition T)
    (A : Finset ℝ≥0) (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i : Fin π.size, (∀ s ∈ A, s ∉ Ioc (π.left i) (π.right i)) →
      ‖Φ (x (π.left i)) (x (π.right i))‖ ≤ C) :
    ‖quadraticPairSum π Φ x T -
      ∑ i : Fin π.size, if ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
        then Φ (x (π.left i)) (x (π.right i)) * (π.increment x i) ^ 2 else 0‖ ≤
      C * quadraticVariationSum π x := by
  classical
  rw [quadraticPairSum_terminal, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin π.size, C * (π.increment x i) ^ 2 := by
      apply sum_le_sum
      intro i _
      by_cases he : ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
      · simp only [if_pos he, sub_self, norm_zero]
        exact mul_nonneg hC (sq_nonneg _)
      · simp only [if_neg he, sub_zero, norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
        exact mul_le_mul_of_nonneg_right
          (hbound i (fun s hs hsc ↦ he ⟨s, hs, hsc⟩)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl

end StochLean
