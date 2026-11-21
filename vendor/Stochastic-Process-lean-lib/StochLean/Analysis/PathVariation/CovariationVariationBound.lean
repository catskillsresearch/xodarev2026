/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.FiniteVariation

/-! # Mixed partition sums controlled by finite variation

The existing `covariationSum` is the pure sum of products of increments: it
contains no initial product. Its norm is bounded by a bound for the first
path's increments times the second path's actual finite variation. A bound
`K` for the first path itself gives the increment bound `2 * K`.

The final theorem separately restores the raw initial product. No path
continuity, square integrability, zero initial value, or new partition/sum
owner is used. Finiteness of the second path's variation is required before
its extended variation is converted to a real number.
-/

@[expose] public section

open Set Finset
open scoped NNReal ENNReal

namespace StochLean

variable {T : ℝ≥0} {x y : ℝ≥0 → ℝ}

/-- The bound uses actual cell increments and the existing variation bound
for their finite absolute sum, not a quadratic-variation moment estimate. -/
theorem norm_covariationSum_le_maxIncrement_mul_variation (π : TimePartition T)
    (hy : BoundedVariationOn y (Icc 0 T)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, ‖π.increment x i‖ ≤ δ) :
    ‖covariationSum π x y‖ ≤ δ * (eVariationOn y (Icc 0 T)).toReal := by
  calc
    ‖covariationSum π x y‖ ≤ ∑ i, ‖π.increment x i * π.increment y i‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖π.increment x i‖ * |π.increment y i| := by
      simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ ∑ i, δ * |π.increment y i| :=
      sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
    _ = δ * ∑ i, |π.increment y i| := (mul_sum ..).symm
    _ ≤ δ * (eVariationOn y (Icc 0 T)).toReal :=
      mul_le_mul_of_nonneg_left (π.sum_abs_increment_le hy) hδ

/-- A bounded first path and a BV second path uniformly control every
finite mixed increment sum, including repeated and empty partition cells. -/
theorem norm_covariationSum_le_of_bounded_left (π : TimePartition T)
    (hy : BoundedVariationOn y (Icc 0 T)) {K : ℝ}
    (hx : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ K) :
    ‖covariationSum π x y‖ ≤ 2 * K * (eVariationOn y (Icc 0 T)).toReal := by
  have hK : 0 ≤ K := (norm_nonneg (x 0)).trans (hx 0 ⟨le_rfl, bot_le⟩)
  apply norm_covariationSum_le_maxIncrement_mul_variation π hy (mul_nonneg (by norm_num) hK)
  intro i
  have hr := hx (π.right i) ⟨bot_le, π.point_le_horizon i.succ⟩
  have hl := hx (π.left i) ⟨bot_le, π.point_le_horizon i.castSucc⟩
  exact (norm_sub_le _ _).trans (by simpa only [two_mul] using add_le_add hr hl)

/-- Raw mixed sums retain their initial product. Its norm cannot be dropped
without a separate initial-value hypothesis. -/
theorem norm_initial_add_covariationSum_le_of_bounded_left (π : TimePartition T)
    (hy : BoundedVariationOn y (Icc 0 T)) {K : ℝ}
    (hx : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ K) :
    ‖x 0 * y 0 + covariationSum π x y‖ ≤
      ‖x 0 * y 0‖ + 2 * K * (eVariationOn y (Icc 0 T)).toReal :=
  (norm_add_le _ _).trans
    (add_le_add le_rfl (norm_covariationSum_le_of_bounded_left π hy hx))

end StochLean
