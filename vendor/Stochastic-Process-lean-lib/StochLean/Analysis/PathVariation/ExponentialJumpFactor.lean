/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.SummableQuadraticRemainder
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # The jump factor of the Doleans--Dade exponential

Square summability implies absolute summability of the deviations from one.
This proves convergence of the actual product, including zero and negative
factors; logarithms are not taken across those exceptional factors.
-/

@[expose] public section

namespace StochLean

noncomputable def exponentialJumpFactor (u : ℝ) : ℝ := (1 + u) * Real.exp (-u)

@[simp] theorem exponentialJumpFactor_zero : exponentialJumpFactor 0 = 1 := by
  simp [exponentialJumpFactor]

@[simp] theorem exponentialJumpFactor_neg_one : exponentialJumpFactor (-1) = 0 := by
  simp [exponentialJumpFactor]

theorem exponentialJumpFactor_eq_zero_iff (u : ℝ) :
    exponentialJumpFactor u = 0 ↔ u = -1 := by
  simp only [exponentialJumpFactor, mul_eq_zero, Real.exp_ne_zero, or_false]
  constructor <;> intro h <;> linarith

theorem exponentialJumpFactor_pos_iff (u : ℝ) : 0 < exponentialJumpFactor u ↔ -1 < u := by
  rw [exponentialJumpFactor, mul_pos_iff_of_pos_right (Real.exp_pos _)]
  constructor <;> intro h <;> linarith

theorem hasDerivAt_exponentialJumpFactor (u : ℝ) :
    HasDerivAt exponentialJumpFactor (-u * Real.exp (-u)) u := by
  have h : HasDerivAt (fun x : ℝ ↦ (1 + x) * Real.exp (-x))
      (1 * Real.exp (-u) + (1 + u) * (Real.exp (-u) * (-1))) u :=
    ((hasDerivAt_id u).const_add 1).mul ((hasDerivAt_id u).neg.exp)
  unfold exponentialJumpFactor
  convert h using 1
  ring

theorem contDiff_exponentialJumpFactor {n : WithTop ℕ∞} :
    ContDiff ℝ n exponentialJumpFactor := by
  unfold exponentialJumpFactor
  fun_prop

theorem summable_abs_exponentialJumpFactor_sub_one {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    Summable (fun i ↦ |exponentialJumpFactor (u i) - 1|) := by
  have hd : deriv exponentialJumpFactor 0 = 0 := by
    simpa using (hasDerivAt_exponentialJumpFactor 0).deriv
  simpa only [exponentialJumpFactor_zero, hd, zero_mul, sub_zero] using
    summable_abs_contDiff_zero_remainder_of_summable_sq hu contDiff_exponentialJumpFactor

theorem multipliable_exponentialJumpFactor {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) : Multipliable (fun i ↦ exponentialJumpFactor (u i)) := by
  have h := Real.multipliable_one_add_of_summable
    (summable_abs_exponentialJumpFactor_sub_one hu).of_abs
  exact h.congr (fun _ ↦ by ring)

end StochLean
