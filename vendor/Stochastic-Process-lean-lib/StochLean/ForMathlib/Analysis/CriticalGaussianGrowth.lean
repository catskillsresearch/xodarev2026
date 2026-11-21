/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # A smooth function with strictly positive Laplacian and critical Gaussian growth

These are calculations for the actual function exp(x^2/2). No subharmonic
predicate is added: the positivity statement uses Mathlib's Laplacian.
-/

@[expose] public section

open InnerProductSpace Laplacian

namespace StochLean

theorem hasDerivAt_exp_half_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (y ^ 2 / 2)) (x * Real.exp (x ^ 2 / 2)) x := by
  convert (((hasDerivAt_id x).pow 2).div_const 2).exp using 1
  · rfl
  · norm_num [Pi.pow_apply, id]
    ring

theorem deriv_deriv_exp_half_sq (x : ℝ) :
    deriv (deriv (fun y : ℝ ↦ Real.exp (y ^ 2 / 2))) x =
      (1 + x ^ 2) * Real.exp (x ^ 2 / 2) := by
  have he : deriv (fun y : ℝ ↦ Real.exp (y ^ 2 / 2)) =
      fun y ↦ y * Real.exp (y ^ 2 / 2) := funext (fun y ↦ (hasDerivAt_exp_half_sq y).deriv)
  rw [he]
  exact ((hasDerivAt_id x).mul (hasDerivAt_exp_half_sq x)).deriv.trans (by
    dsimp only [id]
    ring)

theorem laplacian_exp_half_sq (x : ℝ) :
    Δ (fun y : ℝ ↦ Real.exp (y ^ 2 / 2)) x = (1 + x ^ 2) * Real.exp (x ^ 2 / 2) := by
  rw [laplacian_eq_iteratedDeriv_real]
  change iteratedDeriv (1 + 1) (fun y : ℝ ↦ Real.exp (y ^ 2 / 2)) x = _
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_exp_half_sq]

theorem laplacian_exp_half_sq_pos (x : ℝ) :
    0 < Δ (fun y : ℝ ↦ Real.exp (y ^ 2 / 2)) x := by
  rw [laplacian_exp_half_sq]
  positivity

end StochLean
