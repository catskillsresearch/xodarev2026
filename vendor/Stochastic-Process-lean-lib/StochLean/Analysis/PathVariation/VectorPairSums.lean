/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VectorEnergy

/-! # Endpoint-pair sums weighted by vector increment norms

The sums retain the partial terminal cell. Their energy is bounded by the
coordinate square sums; no vector stochastic quadratic variation is defined.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] {S : ℝ≥0}

noncomputable def normSquarePairSum (π : TimePartition S)
    (Φ : E → E → ℝ) (x : ℝ≥0 → E) (t : ℝ≥0) : ℝ :=
  ∑ i : Fin π.size,
    Φ (x (min (π.left i) t)) (x (min (π.right i) t)) *
      ‖x (min (π.right i) t) - x (min (π.left i) t)‖ ^ 2

@[simp] theorem normSquarePairSum_zero (π : TimePartition S)
    (Φ : E → E → ℝ) (x : ℝ≥0 → E) : normSquarePairSum π Φ x 0 = 0 := by
  simp [normSquarePairSum]

theorem normSquarePairSum_terminal (π : TimePartition S) (Φ : E → E → ℝ)
    (x : ℝ≥0 → E) : normSquarePairSum π Φ x S =
      ∑ i : Fin π.size, Φ (x (π.left i)) (x (π.right i)) *
        ‖x (π.right i) - x (π.left i)‖ ^ 2 := by
  apply sum_congr rfl
  intro i _
  rw [min_eq_left (show π.left i ≤ S from π.point_le_horizon i.castSucc),
    min_eq_left (show π.right i ≤ S from π.point_le_horizon i.succ)]

theorem norm_normSquarePairSum_le (π : TimePartition S)
    (Φ : E → E → ℝ) (x : ℝ≥0 → E) (t : ℝ≥0) {C : ℝ}
    (hC : ∀ i : Fin π.size,
      ‖Φ (x (min (π.left i) t)) (x (min (π.right i) t))‖ ≤ C) :
    ‖normSquarePairSum π Φ x t‖ ≤ C * normSquareVariationSum π (fun u ↦ x (min u t)) := by
  unfold normSquarePairSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin π.size, C *
        ‖x (min (π.right i) t) - x (min (π.left i) t)‖ ^ 2 := by
      apply sum_le_sum
      intro i _
      simp only [norm_mul, norm_pow, norm_norm]
      exact mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl

theorem norm_normSquarePairSum_sub_selected_le (π : TimePartition S)
    (A : Finset ℝ≥0) (Φ : E → E → ℝ) (x : ℝ≥0 → E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i : Fin π.size, (∀ s ∈ A, s ∉ Ioc (π.left i) (π.right i)) →
      ‖Φ (x (π.left i)) (x (π.right i))‖ ≤ C) :
    ‖normSquarePairSum π Φ x S -
      ∑ i : Fin π.size, if ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
        then Φ (x (π.left i)) (x (π.right i)) * ‖x (π.right i) - x (π.left i)‖ ^ 2 else 0‖ ≤
      C * normSquareVariationSum π x := by
  classical
  rw [normSquarePairSum_terminal, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin π.size, C * ‖x (π.right i) - x (π.left i)‖ ^ 2 := by
      apply sum_le_sum
      intro i _
      by_cases he : ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
      · simp only [if_pos he, sub_self, norm_zero]
        exact mul_nonneg hC (sq_nonneg _)
      · simp only [if_neg he, sub_zero, norm_mul, norm_pow, norm_norm]
        exact mul_le_mul_of_nonneg_right
          (hbound i (fun s hs hsc ↦ he ⟨s, hs, hsc⟩)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl

end StochLean
