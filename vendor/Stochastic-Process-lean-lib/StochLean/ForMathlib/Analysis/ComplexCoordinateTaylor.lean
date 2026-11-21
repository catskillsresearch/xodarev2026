/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.ComplexCoordinateDerivatives

/-! # Analytic Taylor jump remainders in the two real coordinates -/

@[expose] public section

namespace StochLean

theorem complex_coordinate_first_order_remainder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (L : ℂ →L[ℝ] ℝ) (a b : Fin 2 → ℝ) :
    L (f (complexCoordinates b)) - L (f (complexCoordinates a)) -
        fderiv ℝ (fun x ↦ L (f (complexCoordinates x))) a (b - a) =
      L (f (complexCoordinates b) - f (complexCoordinates a) -
        deriv f (complexCoordinates a) * (complexCoordinates b - complexCoordinates a)) := by
  rw [fderiv_apply_eq_sum_coordinateDeriv]
  simp only [Fin.sum_univ_two, complex_component_coordinate_gradient hf, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.sub_apply]
  rw [map_sub, map_sub]
  congr 1
  rw [show complexCoordinates b - complexCoordinates a =
    ((b 0 - a 0 : ℝ) : ℂ) + Complex.I * ((b 1 - a 1 : ℝ) : ℂ) by
      simp only [complexCoordinates_apply, Complex.ofReal_sub]; ring]
  have hreal (z : ℂ) (r : ℝ) : L (z * (r : ℂ)) = r * L z := by
    rw [mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul]
  rw [mul_add, ← mul_assoc, map_add, hreal, hreal]
  ring

theorem summable_norm_complex_of_summable_abs_components {α : Type*} {r : α → ℂ}
    (hR : Summable (fun a ↦ |(r a).re|)) (hI : Summable (fun a ↦ |(r a).im|)) :
    Summable (fun a ↦ ‖r a‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun a ↦
    Complex.norm_le_abs_re_add_abs_im (r a)) (hR.add hI)

end StochLean
