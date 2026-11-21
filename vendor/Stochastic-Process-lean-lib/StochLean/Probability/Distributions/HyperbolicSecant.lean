/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.HyperbolicSecantFourier
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.HasLaw

/-! # The zero-safe hyperbolic-secant law for Levy's stochastic area

For positive scale `T`, the density is `1 / (2 T cosh (pi x / (2 T)))`.
The measure at scale zero is Dirac at zero, not the zero-density measure.
Normalization and the inverse-cosh characteristic function follow from the
proved Fourier integral, not from an assumed probability-density certificate.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal InnerProductSpace

namespace ProbabilityTheory

noncomputable def hyperbolicSecantPDFReal (T : ℝ≥0) (x : ℝ) : ℝ :=
  (2 * T * Real.cosh (Real.pi * x / (2 * T)))⁻¹

theorem hyperbolicSecantPDFReal_nonneg (T : ℝ≥0) (x : ℝ) :
    0 ≤ hyperbolicSecantPDFReal T x := by
  unfold hyperbolicSecantPDFReal
  positivity

@[simp] theorem hyperbolicSecantPDFReal_zero (x : ℝ) : hyperbolicSecantPDFReal 0 x = 0 := by
  simp [hyperbolicSecantPDFReal]

theorem continuous_hyperbolicSecantPDFReal (T : ℝ≥0) : Continuous (hyperbolicSecantPDFReal T) := by
  by_cases hT : T = 0
  · subst T
    rw [show hyperbolicSecantPDFReal 0 = fun _ ↦ 0 from funext hyperbolicSecantPDFReal_zero]
    exact continuous_const
  · apply Continuous.inv₀ (by fun_prop)
    intro x
    exact mul_ne_zero (mul_ne_zero (by norm_num) (NNReal.coe_ne_zero.mpr hT))
      (Real.cosh_pos _).ne'

theorem integral_hyperbolicSecantPDFReal {T : ℝ≥0} (hT : T ≠ 0) :
    (∫ x : ℝ, hyperbolicSecantPDFReal T x) = 1 := by
  have hi := StochLean.integral_exp_mul_I_div_scaled_cosh 0
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT))
  apply Complex.ofReal_injective
  calc
    _ = ∫ x : ℝ, (hyperbolicSecantPDFReal T x : ℂ) := integral_ofReal.symm
    _ = _ := by
      simpa only [zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero, Real.cosh_zero,
        Complex.ofReal_one, inv_one, one_div, hyperbolicSecantPDFReal, Complex.ofReal_inv] using hi

theorem integrable_hyperbolicSecantPDFReal (T : ℝ≥0) : Integrable (hyperbolicSecantPDFReal T) := by
  by_cases hT : T = 0
  · subst T
    rw [show hyperbolicSecantPDFReal 0 = fun _ ↦ 0 from funext hyperbolicSecantPDFReal_zero]
    exact integrable_zero ℝ ℝ volume
  · apply Integrable.of_integral_ne_zero
    rw [integral_hyperbolicSecantPDFReal hT]
    exact one_ne_zero

noncomputable def hyperbolicSecantPDF (T : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (hyperbolicSecantPDFReal T x)

theorem measurable_hyperbolicSecantPDF (T : ℝ≥0) : Measurable (hyperbolicSecantPDF T) :=
  ENNReal.measurable_ofReal.comp (continuous_hyperbolicSecantPDFReal T).measurable

@[simp] theorem lintegral_hyperbolicSecantPDF {T : ℝ≥0} (hT : T ≠ 0) :
    (∫⁻ x : ℝ, hyperbolicSecantPDF T x) = 1 := by
  unfold hyperbolicSecantPDF
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (hyperbolicSecantPDFReal_nonneg T))
    (continuous_hyperbolicSecantPDFReal T).measurable.aestronglyMeasurable,
    integral_hyperbolicSecantPDFReal hT]

noncomputable def hyperbolicSecantMeasure (T : ℝ≥0) : Measure ℝ :=
  if T = 0 then Measure.dirac 0 else volume.withDensity (hyperbolicSecantPDF T)

@[simp] theorem hyperbolicSecantMeasure_zero : hyperbolicSecantMeasure 0 = Measure.dirac 0 :=
  if_pos rfl

theorem hyperbolicSecantMeasure_of_ne_zero {T : ℝ≥0} (hT : T ≠ 0) :
    hyperbolicSecantMeasure T = volume.withDensity (hyperbolicSecantPDF T) := if_neg hT

instance instIsProbabilityMeasure_hyperbolicSecantMeasure (T : ℝ≥0) :
    IsProbabilityMeasure (hyperbolicSecantMeasure T) where
  measure_univ := by
    by_cases hT : T = 0
    · subst T
      simp
    · simp [hyperbolicSecantMeasure_of_ne_zero hT, lintegral_hyperbolicSecantPDF hT]

theorem charFun_hyperbolicSecantMeasure (T : ℝ≥0) (u : ℝ) :
    charFun (hyperbolicSecantMeasure T) u = ((Real.cosh (u * T))⁻¹ : ℂ) := by
  by_cases hT : T = 0
  · subst T
    simp [charFun_apply]
  · rw [charFun_apply, hyperbolicSecantMeasure_of_ne_zero hT,
      integral_withDensity_eq_integral_toReal_smul (measurable_hyperbolicSecantPDF T)
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    have he (x : ℝ) : (hyperbolicSecantPDF T x).toReal •
        Complex.exp ((↑⟪x, u⟫_ℝ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) /
        ((2 * T * Real.cosh (Real.pi * x / (2 * T)) : ℝ) : ℂ) := by
      rw [hyperbolicSecantPDF, ENNReal.toReal_ofReal (hyperbolicSecantPDFReal_nonneg T x)]
      simp only [hyperbolicSecantPDFReal, Complex.real_smul, Complex.ofReal_inv,
        RCLike.inner_apply, conj_trivial, Complex.ofReal_mul]
      rw [show (u : ℂ) * (x : ℂ) * Complex.I = Complex.I * ((u : ℂ) * (x : ℂ)) by ring]
      ring
    simp_rw [he]
    exact StochLean.integral_exp_mul_I_div_scaled_cosh u
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT))

theorem hasLaw_hyperbolicSecant_of_integral_exp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : AEMeasurable Y P) (T : ℝ≥0)
    (h : ∀ u : ℝ, (∫ ω, Complex.exp (Complex.I * (u : ℂ) * (Y ω : ℂ)) ∂P) =
      ((Real.cosh (u * T))⁻¹ : ℂ)) : HasLaw Y (hyperbolicSecantMeasure T) P := by
  refine ⟨hY, Measure.ext_of_charFun ?_⟩
  funext u
  rw [charFun_apply, integral_map hY (by fun_prop), charFun_hyperbolicSecantMeasure]
  simpa only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul, mul_comm, mul_left_comm,
    mul_assoc] using h u

end ProbabilityTheory
