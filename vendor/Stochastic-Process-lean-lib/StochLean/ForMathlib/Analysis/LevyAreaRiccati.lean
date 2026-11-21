/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The terminal Riccati coefficients for Levy's stochastic area

These are the actual smooth hyperbolic functions in Protter II.43, for every
real Fourier parameter, including zero and negative parameters. Their signs
on the backward time interval give the deterministic bound on the exponential.
No stochastic-area law or local-martingale conclusion is assumed here.
-/

@[expose] public section

namespace StochLean

noncomputable def levyAreaAlpha (u T t : ℝ) : ℝ := u * Real.tanh (u * (T - t))

noncomputable def levyAreaBeta (u T t : ℝ) : ℝ := -Real.log (Real.cosh (u * (T - t)))

theorem hasDerivAt_real_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  rw [show Real.tanh = Real.sinh / Real.cosh from
    funext fun y ↦ Real.tanh_eq_sinh_div_cosh y]
  apply ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x))).congr_deriv
  simp only [Pi.div_apply]
  field_simp

theorem contDiff_real_tanh {n : WithTop ℕ∞} : ContDiff ℝ n Real.tanh := by
  rw [show Real.tanh = Real.sinh / Real.cosh from
    funext fun y ↦ Real.tanh_eq_sinh_div_cosh y]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x ↦ ne_of_gt (Real.cosh_pos x))

theorem hasDerivAt_levyAreaAlpha (u T t : ℝ) :
    HasDerivAt (levyAreaAlpha u T) (levyAreaAlpha u T t ^ 2 - u ^ 2) t := by
  have hv : HasDerivAt (fun r : ℝ ↦ u * (T - r)) (-u) t := by
    exact (((hasDerivAt_id t).const_sub T).const_mul u).congr_deriv (by ring)
  apply (((hasDerivAt_real_tanh _).comp t hv).const_mul u).congr_deriv
  dsimp only [levyAreaAlpha]
  ring

theorem hasDerivAt_levyAreaBeta (u T t : ℝ) :
    HasDerivAt (levyAreaBeta u T) (levyAreaAlpha u T t) t := by
  have hv : HasDerivAt (fun r : ℝ ↦ u * (T - r)) (-u) t := by
    exact (((hasDerivAt_id t).const_sub T).const_mul u).congr_deriv (by ring)
  apply ((((Real.hasDerivAt_cosh _).comp t hv).log
    (ne_of_gt (Real.cosh_pos _))).neg).congr_deriv
  dsimp only [levyAreaAlpha, Function.comp_apply]
  rw [Real.tanh_eq_sinh_div_cosh]
  ring

theorem contDiff_levyAreaAlpha (u T : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (levyAreaAlpha u T) :=
  contDiff_const.mul (contDiff_real_tanh.comp (contDiff_const.mul
    (contDiff_const.sub contDiff_id)))

theorem contDiff_levyAreaBeta (u T : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (levyAreaBeta u T) :=
  ((Real.contDiff_cosh.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))).log
    (fun t ↦ ne_of_gt (Real.cosh_pos (u * (T - t))))).neg

@[simp] theorem levyAreaAlpha_terminal (u T : ℝ) : levyAreaAlpha u T T = 0 := by
  simp [levyAreaAlpha]

@[simp] theorem levyAreaBeta_terminal (u T : ℝ) : levyAreaBeta u T T = 0 := by
  simp [levyAreaBeta]

@[simp] theorem levyAreaAlpha_zero (T t : ℝ) : levyAreaAlpha 0 T t = 0 := by
  simp [levyAreaAlpha]

@[simp] theorem levyAreaBeta_zero (T t : ℝ) : levyAreaBeta 0 T t = 0 := by
  simp [levyAreaBeta]

theorem levyAreaAlpha_nonneg (u : ℝ) {T t : ℝ} (ht : t ≤ T) :
    0 ≤ levyAreaAlpha u T t := by
  rw [levyAreaAlpha, Real.tanh_eq_sinh_div_cosh]
  rcases le_total 0 u with hu | hu
  · exact mul_nonneg hu (div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hu (sub_nonneg.mpr ht))) (Real.cosh_pos _).le)
  · exact mul_nonneg_of_nonpos_of_nonpos hu (div_nonpos_of_nonpos_of_nonneg
      (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hu (sub_nonneg.mpr ht)))
      (Real.cosh_pos _).le)

theorem levyAreaBeta_nonpos (u T t : ℝ) : levyAreaBeta u T t ≤ 0 :=
  neg_nonpos.mpr (Real.log_nonneg (Real.one_le_cosh _))

theorem exp_levyAreaBeta (u T t : ℝ) :
    Real.exp (levyAreaBeta u T t) = (Real.cosh (u * (T - t)))⁻¹ := by
  rw [levyAreaBeta, Real.exp_neg, Real.exp_log (Real.cosh_pos _)]

theorem levyArea_coefficient_square_sum (u a x y : ℝ) :
    (-Complex.I * (u : ℂ) * y - (a : ℂ) * x) ^ 2 +
      (Complex.I * (u : ℂ) * x - (a : ℂ) * y) ^ 2 =
        ((a : ℂ) ^ 2 - (u : ℂ) ^ 2) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) := by
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem norm_exp_levyAreaExponent_le_one (u a x y : ℝ) {T t : ℝ} (ht : t ≤ T) :
    ‖Complex.exp (Complex.I * (u : ℂ) * a -
      (levyAreaAlpha u T t : ℂ) / 2 * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) +
        (levyAreaBeta u T t : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, zero_mul, mul_zero, zero_sub, sub_zero, zero_add,
    ← Complex.ofReal_pow, ← Complex.ofReal_add]
  have hα := levyAreaAlpha_nonneg u ht
  have hβ := levyAreaBeta_nonpos u T t
  nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hα (add_nonneg (sq_nonneg x) (sq_nonneg y))]

end StochLean
