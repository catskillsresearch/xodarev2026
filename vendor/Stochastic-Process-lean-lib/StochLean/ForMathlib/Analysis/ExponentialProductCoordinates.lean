/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.FiniteCoordinateSecondDerivative
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The actual gradient and Hessian of the exponential-times-linear map

The two coordinates are the compensated integrator and its jump-product
factor. All ordered Hessian entries are retained before the stochastic
finite-variation bracket identities remove the mixed and second entries.
-/

@[expose] public section

namespace StochLean

noncomputable def exponentialProductCoordinates (x : Fin 2 → ℝ) : ℝ := Real.exp (x 0) * x 1

theorem contDiff_exponentialProductCoordinates {n : WithTop ℕ∞} :
    ContDiff ℝ n exponentialProductCoordinates := by
  unfold exponentialProductCoordinates
  fun_prop

theorem coordinateDeriv_exp_first (x : Fin 2 → ℝ) (i : Fin 2) :
    coordinateDeriv (fun y : Fin 2 → ℝ ↦ Real.exp (y 0)) i x =
      ![Real.exp (x 0), 0] i := by
  have h0 : HasFDerivAt (fun y : Fin 2 → ℝ ↦ y 0) (ContinuousLinearMap.proj 0) x :=
    (show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 0).hasFDerivAt
  rw [coordinateDeriv, h0.exp.fderiv]
  fin_cases i <;> simp

theorem coordinateDeriv_exponentialProductCoordinates (x : Fin 2 → ℝ) (i : Fin 2) :
    coordinateDeriv exponentialProductCoordinates i x =
      ![exponentialProductCoordinates x, Real.exp (x 0)] i := by
  have h0 : HasFDerivAt (fun y : Fin 2 → ℝ ↦ y 0) (ContinuousLinearMap.proj 0) x :=
    (show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 0).hasFDerivAt
  have h1 : HasFDerivAt (fun y : Fin 2 → ℝ ↦ y 1) (ContinuousLinearMap.proj 1) x :=
    (show (Fin 2 → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj 1).hasFDerivAt
  have hd : HasFDerivAt exponentialProductCoordinates
      (Real.exp (x 0) • ContinuousLinearMap.proj (1 : Fin 2) +
        x 1 • (Real.exp (x 0) • ContinuousLinearMap.proj (0 : Fin 2))) x := h0.exp.mul h1
  rw [coordinateDeriv, hd.fderiv]
  fin_cases i <;> simp [exponentialProductCoordinates, mul_comm]

theorem coordinateSecondDeriv_exponentialProductCoordinates (x : Fin 2 → ℝ) (i j : Fin 2) :
    coordinateSecondDeriv exponentialProductCoordinates i j x =
      ![![exponentialProductCoordinates x, Real.exp (x 0)], ![Real.exp (x 0), 0]] i j := by
  rw [← coordinateDeriv_coordinateDeriv contDiff_exponentialProductCoordinates]
  fin_cases j
  · change coordinateDeriv (coordinateDeriv exponentialProductCoordinates 0) i x =
      ![![exponentialProductCoordinates x, Real.exp (x 0)], ![Real.exp (x 0), 0]] i 0
    have he : coordinateDeriv exponentialProductCoordinates 0 =
        exponentialProductCoordinates := by
      funext y
      simp only [coordinateDeriv_exponentialProductCoordinates, Matrix.cons_val_zero]
    rw [he, coordinateDeriv_exponentialProductCoordinates]
    fin_cases i <;> simp
  · change coordinateDeriv (coordinateDeriv exponentialProductCoordinates 1) i x =
      ![![exponentialProductCoordinates x, Real.exp (x 0)], ![Real.exp (x 0), 0]] i 1
    have he : coordinateDeriv exponentialProductCoordinates 1 =
        fun y ↦ Real.exp (y 0) := by
      funext y
      simp only [coordinateDeriv_exponentialProductCoordinates, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    rw [he, coordinateDeriv_exp_first]
    fin_cases i <;> simp

end StochLean
