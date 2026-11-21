/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.FiniteCoordinateSecondDerivative
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Real coordinate derivatives of complex analytic functions

The coordinate map sends (x,y) to x + iy. Real and imaginary components
are handled uniformly by a real continuous linear functional. The two
Hessian indices are ordered, and the second imaginary derivative has its
actual negative sign through I squared.
-/

@[expose] public section

namespace StochLean

noncomputable def complexCoordinates : (Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0) +
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)

@[simp] theorem complexCoordinates_apply (x : Fin 2 → ℝ) :
    complexCoordinates x = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := by
  simp [complexCoordinates, smul_eq_mul]

@[simp] theorem complexCoordinates_single_zero :
    complexCoordinates (Pi.single (0 : Fin 2) 1) = 1 := by simp

@[simp] theorem complexCoordinates_single_one :
    complexCoordinates (Pi.single (1 : Fin 2) 1) = Complex.I := by simp

theorem contDiff_complex_coordinate_component {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (L : ℂ →L[ℝ] ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : Fin 2 → ℝ ↦ L (f (complexCoordinates x))) :=
  L.contDiff.comp ((hf.contDiff.restrict_scalars ℝ).comp complexCoordinates.contDiff)

theorem coordinateDeriv_complex_component {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (L : ℂ →L[ℝ] ℝ) (i : Fin 2) (x : Fin 2 → ℝ) :
    coordinateDeriv (fun y ↦ L (f (complexCoordinates y))) i x =
      L (deriv f (complexCoordinates x) * complexCoordinates (Pi.single i 1)) := by
  have h := L.hasFDerivAt.comp x
    (((hf (complexCoordinates x)).hasDerivAt.complexToReal_fderiv).comp x
      complexCoordinates.hasFDerivAt)
  simp only [Function.comp_def] at h
  rw [coordinateDeriv, h.fderiv]
  simp

theorem coordinateSecondDeriv_complex_component {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (L : ℂ →L[ℝ] ℝ) (i j : Fin 2) (x : Fin 2 → ℝ) :
    coordinateSecondDeriv (fun y ↦ L (f (complexCoordinates y))) i j x =
      L (deriv (deriv f) (complexCoordinates x) * complexCoordinates (Pi.single i 1) *
        complexCoordinates (Pi.single j 1)) := by
  rw [← coordinateDeriv_coordinateDeriv (contDiff_complex_coordinate_component hf L)]
  let M : ℂ →L[ℝ] ℝ := L.comp
    (complexCoordinates (Pi.single j 1) • (1 : ℂ →L[ℝ] ℂ))
  have he : coordinateDeriv (fun y ↦ L (f (complexCoordinates y))) j =
      fun y ↦ M (deriv f (complexCoordinates y)) := by
    funext y
    rw [coordinateDeriv_complex_component hf]
    simp only [M, ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self, smul_eq_mul]
    rw [mul_comm]
  rw [he, coordinateDeriv_complex_component hf.deriv M]
  simp only [M, ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self, smul_eq_mul]
  congr 1
  ring

theorem complex_component_coordinate_gradient {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (L : ℂ →L[ℝ] ℝ) (x : Fin 2 → ℝ) (i : Fin 2) :
    coordinateDeriv (fun y ↦ L (f (complexCoordinates y))) i x =
      ![L (deriv f (complexCoordinates x)),
        L (deriv f (complexCoordinates x) * Complex.I)] i := by
  rw [coordinateDeriv_complex_component hf]
  fin_cases i <;> simp

theorem complex_component_coordinate_hessian {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (L : ℂ →L[ℝ] ℝ) (x : Fin 2 → ℝ) (i j : Fin 2) :
    coordinateSecondDeriv (fun y ↦ L (f (complexCoordinates y))) i j x =
      ![![L (deriv (deriv f) (complexCoordinates x)),
          L (deriv (deriv f) (complexCoordinates x) * Complex.I)],
        ![L (deriv (deriv f) (complexCoordinates x) * Complex.I),
          -L (deriv (deriv f) (complexCoordinates x))]] i j := by
  rw [coordinateSecondDeriv_complex_component hf]
  fin_cases i <;> fin_cases j <;> simp [mul_assoc]

end StochLean
