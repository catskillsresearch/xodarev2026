/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Basic
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue

/-! # Complex stochastic integration by the existing real integral

A complex integrand against a real integrator is integrated coordinatewise.
A complex integrator is then handled by linearity in its real and imaginary
parts. These definitions do not construct any new integration extension.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z H : ℝ≥0 → Ω → ℂ}

noncomputable def IsSemimartingale.complexIntegrandIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) : ℝ≥0 → Ω → ℂ :=
  complexProcess
    (hX.stochasticIntegral hF (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_re))
    (hX.stochasticIntegral hF (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im))

theorem IsSemimartingale.isComplexSemimartingale_complexIntegrandIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsComplexSemimartingale (hX.complexIntegrandIntegral hF ha hr) F P :=
  (hX.isSemimartingale_stochasticIntegral hF
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re)).complex
      (hX.isSemimartingale_stochasticIntegral hF
        (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
        (hr.continuous_comp Complex.continuous_im))

theorem IsSemimartingale.complexIntegrandIntegral_zero_ae
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    hX.complexIntegrandIntegral hF ha hr 0 =ᵐ[P] fun ω ↦ H 0 ω * (X 0 ω : ℂ) := by
  filter_upwards [hX.stochasticIntegral_zero_ae hF
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re), hX.stochasticIntegral_zero_ae hF
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im)] with ω hR hI
  apply Complex.ext <;> simp [complexIntegrandIntegral, complexProcess, hR, hI]

noncomputable def IsComplexSemimartingale.stochasticIntegral
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) : ℝ≥0 → Ω → ℂ :=
  hZ.1.complexIntegrandIntegral hF ha hr + Complex.I • hZ.2.complexIntegrandIntegral hF ha hr

theorem IsComplexSemimartingale.isComplexSemimartingale_stochasticIntegral
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsComplexSemimartingale (hZ.stochasticIntegral hF ha hr) F P :=
  (hZ.1.isComplexSemimartingale_complexIntegrandIntegral hF ha hr).add
    ((hZ.2.isComplexSemimartingale_complexIntegrandIntegral hF ha hr).const_mul Complex.I)

theorem IsComplexSemimartingale.stochasticIntegral_zero_ae
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    hZ.stochasticIntegral hF ha hr 0 =ᵐ[P] fun ω ↦ H 0 ω * Z 0 ω := by
  filter_upwards [hZ.1.complexIntegrandIntegral_zero_ae hF ha hr,
    hZ.2.complexIntegrandIntegral_zero_ae hF ha hr] with ω hR hI
  simp only [stochasticIntegral, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hR, hI]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end ProbabilityTheory
