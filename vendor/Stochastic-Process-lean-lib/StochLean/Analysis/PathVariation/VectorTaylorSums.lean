/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VectorPairSums
public import StochLean.ForMathlib.Analysis.FrechetTaylorCoefficient

/-! # Exact Frechet Taylor sums with partial terminal cells

Derivatives are sampled at the original left endpoint. After the evaluation
time, zero increments remove their contributions without moving the sample.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : ℝ≥0}

noncomputable def frechetTaylorErrorSum (π : TimePartition S) (f : E → ℝ)
    (x : ℝ≥0 → E) : ℝ≥0 → ℝ := normSquarePairSum π (frechetTaylorErrorCoefficient f) x

theorem TimePartition.frechet_taylor_sum_with_remainder (π : TimePartition S)
    (f : E → ℝ) (x : ℝ≥0 → E) (t : ℝ≥0) :
    f (x (min S t)) - f (x 0) =
      (∑ i : Fin π.size, fderiv ℝ f (x (π.left i))
        (x (min (π.right i) t) - x (min (π.left i) t))) +
      (1 / 2 : ℝ) * (∑ i : Fin π.size, fderiv ℝ (fderiv ℝ f) (x (π.left i))
        (x (min (π.right i) t) - x (min (π.left i) t))
        (x (min (π.right i) t) - x (min (π.left i) t))) +
      frechetTaylorErrorSum π f x t := by
  have ht : (∑ i : Fin π.size,
      (f (x (min (π.right i) t)) - f (x (min (π.left i) t)))) =
      f (x (min S t)) - f (x 0) := by
    simpa only [TimePartition.increment, zero_min] using
      π.sum_increment (fun u ↦ f (x (min u t)))
  rw [← ht, frechetTaylorErrorSum, normSquarePairSum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [frechetTaylorErrorCoefficient_mul_norm_sq]
  by_cases hi : π.left i ≤ t
  · rw [min_eq_left hi, frechetSecondOrderRemainder]
    ring
  · have hl : t ≤ π.left i := (lt_of_not_ge hi).le
    have hr : t ≤ π.right i := hl.trans (π.left_le_right i)
    simp only [min_eq_right hl, min_eq_right hr, sub_self, map_zero,
      mul_zero, add_zero, frechetSecondOrderRemainder_self]

end StochLean
