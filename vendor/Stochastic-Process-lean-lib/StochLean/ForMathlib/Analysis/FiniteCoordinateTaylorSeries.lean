/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.FiniteCoordinateDerivatives
public import StochLean.ForMathlib.Analysis.FrechetTaylorCoefficient
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Converting absolutely summable finite-coordinate Taylor corrections

Only finite sums and genuinely summable series are interchanged. No smoothness
is needed for this algebraic identity; analytic summability is supplied by callers.
-/

@[expose] public section

open Finset

namespace StochLean

theorem tsum_frechetSecondOrderRemainder_eq_coordinate_correction
    {ι α : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ) (a b : α → ι → ℝ)
    (hR : Summable (fun s ↦ f (b s) - f (a s) - fderiv ℝ f (a s) (b s - a s)))
    (hH : ∀ i j, Summable (fun s ↦
      coordinateSecondDeriv f i j (a s) * (b s i - a s i) * (b s j - a s j))) :
    (∑' s, frechetSecondOrderRemainder f (a s) (b s)) =
      (∑' s, (f (b s) - f (a s) - fderiv ℝ f (a s) (b s - a s))) -
        (1 / 2 : ℝ) * ∑ i, ∑ j, ∑' s,
          coordinateSecondDeriv f i j (a s) * (b s i - a s i) * (b s j - a s j) := by
  have hsum : Summable (fun s ↦ ∑ i, ∑ j,
      coordinateSecondDeriv f i j (a s) * (b s i - a s i) * (b s j - a s j)) :=
    summable_sum (fun i _ ↦ summable_sum (fun j _ ↦ hH i j))
  simp only [frechetSecondOrderRemainder, second_fderiv_apply_eq_sum_coordinateSecondDeriv,
    Pi.sub_apply]
  rw [hR.tsum_sub (hsum.mul_left (1 / 2 : ℝ)), hsum.tsum_mul_left]
  congr 1
  congr 1
  rw [Summable.tsum_finsetSum (fun i _ ↦ summable_sum (fun j _ ↦ hH i j))]
  apply sum_congr rfl
  intro i _
  exact Summable.tsum_finsetSum (fun j _ ↦ hH i j)

end StochLean
