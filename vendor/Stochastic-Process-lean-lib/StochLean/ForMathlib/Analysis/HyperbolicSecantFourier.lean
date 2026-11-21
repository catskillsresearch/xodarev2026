/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The hyperbolic-secant Fourier integral

Euler's beta integral and Gamma reflection formula supply the analytic
identity needed for the positive-time Levy stochastic-area density.
The sigmoid substitution uses the existing one-dimensional Jacobian theorem.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace StochLean

theorem betaIntegral_half_add_mul_I (a : ℝ) :
    Complex.betaIntegral ((1 / 2 : ℂ) + (a : ℂ) * Complex.I)
      (1 - ((1 / 2 : ℂ) + (a : ℂ) * Complex.I)) =
        (Real.pi / Real.cosh (Real.pi * a) : ℂ) := by
  let s : ℂ := 1 / 2 + (a : ℂ) * Complex.I
  have hs : 0 < s.re := by simp [s]
  have ht : 0 < (1 - s).re := by norm_num [s]
  have hb := Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul,
    Complex.Gamma_mul_Gamma_one_sub] at hb
  have he : (Real.pi : ℂ) * s = (Real.pi : ℂ) / 2 +
      ((Real.pi * a : ℝ) : ℂ) * Complex.I := by
    dsimp only [s]
    push_cast
    ring
  rw [← hb, he, Complex.sin_add_mul_I]
  simp

private theorem log_sigmoid_two_mul (x : ℝ) :
    Real.log (Real.sigmoid (2 * x)) = 2 * x - Real.log (1 + Real.exp (2 * x)) := by
  have he : Real.sigmoid (2 * x) = Real.exp (2 * x) / (1 + Real.exp (2 * x)) := by
    rw [Real.sigmoid_def, Real.exp_neg]
    field_simp
    ring
  rw [he, Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp]

private theorem log_one_sub_sigmoid_two_mul (x : ℝ) :
    Real.log (1 - Real.sigmoid (2 * x)) = -Real.log (1 + Real.exp (2 * x)) := by
  rw [← Real.sigmoid_neg, Real.sigmoid_def, neg_neg, Real.log_inv]

private theorem weighted_beta_kernel (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s t : ℂ) :
    (a * b) • ((a : ℂ) ^ (s - 1) * (b : ℂ) ^ (t - 1)) =
      Complex.exp ((Real.log a : ℂ) * s + (Real.log b : ℂ) * t) := by
  have hca : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hcb : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Complex.cpow_def_of_ne_zero hca, Complex.cpow_def_of_ne_zero hcb,
    ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le,
    Complex.real_smul, Complex.ofReal_mul]
  have hea : (a : ℂ) = Complex.exp (Real.log a : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log ha]
  have heb : (b : ℂ) = Complex.exp (Real.log b : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hb]
  rw [hea, heb, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

private theorem sigmoid_two_mul_beta_kernel (a x : ℝ) :
    let q := Real.sigmoid (2 * x)
    let s : ℂ := 1 / 2 + (a : ℂ) * Complex.I
    (2 * q * (1 - q)) • ((q : ℂ) ^ (s - 1) * (1 - (q : ℂ)) ^ ((1 - s) - 1)) =
      Complex.exp (Complex.I * ((2 * a * x : ℝ) : ℂ)) / (Real.cosh x : ℂ) := by
  let q := Real.sigmoid (2 * x)
  let s : ℂ := 1 / 2 + (a : ℂ) * Complex.I
  have hq : 0 < q := Real.sigmoid_pos _
  have hqb : 0 < 1 - q := sub_pos.mpr (Real.sigmoid_lt_one _)
  have hw := weighted_beta_kernel q (1 - q) hq hqb s (1 - s)
  have he : (Real.log q : ℂ) * s + (Real.log (1 - q) : ℂ) * (1 - s) =
      (x : ℂ) + Complex.I * ((2 * a * x : ℝ) : ℂ) -
        (Real.log (1 + Real.exp (2 * x)) : ℂ) := by
    dsimp only [q, s]
    rw [log_sigmoid_two_mul, log_one_sub_sigmoid_two_mul]
    push_cast
    ring
  have hd : (1 + Real.exp (2 * x) : ℝ) = 2 * Real.exp x * Real.cosh x := by
    rw [Real.cosh_eq]
    field_simp
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
    simp [add_comm]
  change (2 * q * (1 - q)) • _ = _
  calc
    _ = (2 : ℝ) • ((q * (1 - q)) •
        ((q : ℂ) ^ (s - 1) * ((1 - q : ℝ) : ℂ) ^ ((1 - s) - 1))) := by
      rw [smul_smul]
      push_cast
      congr 1
      ring
    _ = (2 : ℝ) • Complex.exp ((x : ℂ) + Complex.I * ((2 * a * x : ℝ) : ℂ) -
        (Real.log (1 + Real.exp (2 * x)) : ℂ)) := by rw [hw, he]
    _ = _ := by
      rw [Complex.exp_sub, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
        Real.exp_log (by positivity : 0 < 1 + Real.exp (2 * x)),
        Complex.real_smul, Complex.ofReal_ofNat, hd]
      push_cast
      field_simp

theorem integral_exp_mul_I_div_cosh (u : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) / (Real.cosh x : ℂ)) =
      (Real.pi / Real.cosh (Real.pi * u / 2) : ℂ) := by
  let f : ℝ → ℝ := fun x ↦ Real.sigmoid (2 * x)
  let f' : ℝ → ℝ := fun x ↦ 2 * f x * (1 - f x)
  let s : ℂ := 1 / 2 + ((u / 2 : ℝ) : ℂ) * Complex.I
  let g : ℝ → ℂ := fun y ↦ (y : ℂ) ^ (s - 1) * (1 - (y : ℂ)) ^ ((1 - s) - 1)
  have hd (x : ℝ) : HasDerivAt f (f' x) x := by
    exact ((Real.hasDerivAt_sigmoid (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2)).congr_deriv (by dsimp only [f', f]; ring)
  have hr : f '' univ = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      exact ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩
    · intro hy
      obtain ⟨x, hx⟩ := (show y ∈ range Real.sigmoid by rwa [Real.range_sigmoid])
      refine ⟨x / 2, mem_univ _, ?_⟩
      simpa only [f, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hx
  have hi : InjOn f univ := by
    intro x _ y _ h
    have he := Real.sigmoid_injective h
    linarith
  have hc (x : ℝ) : |f' x| • g (f x) =
      Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) / (Real.cosh x : ℂ) := by
    have hp : 0 ≤ f' x := mul_nonneg (mul_nonneg (by norm_num) (Real.sigmoid_nonneg _))
      (sub_nonneg.mpr (Real.sigmoid_le_one _))
    rw [abs_of_nonneg hp]
    have hk := sigmoid_two_mul_beta_kernel (u / 2) x
    simpa only [show 2 * (u / 2) * x = u * x by ring] using hk
  have hj := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hd x).hasDerivWithinAt) hi g
  rw [hr, Measure.restrict_univ] at hj
  simp_rw [hc] at hj
  calc
    _ = ∫ y in Ioo 0 1, g y := hj.symm
    _ = Complex.betaIntegral s (1 - s) := by
      rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
    _ = (Real.pi / Real.cosh (Real.pi * (u / 2)) : ℂ) := betaIntegral_half_add_mul_I (u / 2)
    _ = _ := by rw [mul_div_assoc]

theorem integrable_exp_mul_I_div_cosh (u : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) /
      (Real.cosh x : ℂ)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_mul_I_div_cosh]
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')

theorem integral_exp_mul_I_div_scaled_cosh (u : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ x : ℝ, Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) /
      ((2 * T * Real.cosh (Real.pi * x / (2 * T)) : ℝ) : ℂ)) =
        ((Real.cosh (u * T))⁻¹ : ℂ) := by
  let c : ℝ := Real.pi / (2 * T)
  have hc : 0 < c := div_pos Real.pi_pos (mul_pos (by norm_num) hT)
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ Complex.exp (Complex.I * (((u / c) * x : ℝ) : ℂ)) /
      (Real.cosh x : ℂ)) c
  rw [integral_exp_mul_I_div_cosh, abs_of_pos (inv_pos.mpr hc)] at hscale
  have hphase (x : ℝ) : (u / c) * (c * x) = u * x := by field_simp
  have harg (x : ℝ) : c * x = Real.pi * x / (2 * T) := by dsimp only [c]; ring
  have hterminal : Real.pi * (u / c) / 2 = u * T := by
    dsimp only [c]
    field_simp
  simp_rw [hphase, harg, hterminal] at hscale
  calc
    _ = ((2 * T : ℝ) : ℂ)⁻¹ * ∫ x : ℝ,
        Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) /
          (Real.cosh (Real.pi * x / (2 * T)) : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by push_cast; ring
    _ = _ := by
      rw [hscale, Complex.real_smul]
      dsimp only [c]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hT.ne']

theorem integrable_exp_mul_I_div_scaled_cosh (u : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun x : ℝ ↦ Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) /
      ((2 * T * Real.cosh (Real.pi * x / (2 * T)) : ℝ) : ℂ)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_mul_I_div_scaled_cosh u hT]
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')

end StochLean
