/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ExponentialJumpFactor

/-! # Multiplication of the actual stochastic-exponential jump products

The compensated product identity includes zero and negative factors. Mixed
jump summability supplies the exponential correction, without logarithms.
-/

@[expose] public section

namespace StochLean

theorem exponentialJumpFactor_add_add_mul (u v : ℝ) :
    exponentialJumpFactor (u + v + u * v) =
      exponentialJumpFactor u * exponentialJumpFactor v * Real.exp (-(u * v)) := by
  simp only [exponentialJumpFactor, neg_add, Real.exp_add]
  ring

theorem tprod_exponentialJumpFactor_add_add_mul {ι : Type*} {u v : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) (hv : Summable (fun i ↦ v i ^ 2))
    (hm : Summable (fun i ↦ u i * v i)) :
    (∏' i, exponentialJumpFactor (u i + v i + u i * v i)) =
      (∏' i, exponentialJumpFactor (u i)) * (∏' i, exponentialJumpFactor (v i)) *
        Real.exp (-(∑' i, u i * v i)) := by
  have he : HasProd (fun i ↦ Real.exp (-(u i * v i)))
      (Real.exp (-(∑' i, u i * v i))) := by
    simpa only [Function.comp_def, tsum_neg] using hm.neg.hasSum.rexp
  have hp := ((multipliable_exponentialJumpFactor hu).hasProd.mul
    (multipliable_exponentialJumpFactor hv).hasProd).mul he
  exact (hp.congr_fun (fun i ↦ exponentialJumpFactor_add_add_mul (u i) (v i))).tprod_eq

end StochLean
