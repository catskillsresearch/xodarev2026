/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.QuadraticVariation
public import StochLean.Probability.Process.Semimartingale.Complex.IntegratorAlgebra

/-! # Coordinate reduction of integration against complex bilinear brackets

The two ordered mixed contributions produce the factor two. The real
energy bracket is deliberately not used in these analytic identities.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z H : ℝ≥0 → Ω → ℂ}

theorem IsComplexSemimartingale.stochasticIntegral_quadraticVariation_coordinates
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hZ.isComplexSemimartingale_quadraticVariation hF).stochasticIntegral hF ha hr)
      (fun t ω ↦
        (hZ.1.isSemimartingale_quadraticVariation hF).complexIntegrandIntegral hF ha hr t ω -
        (hZ.2.isSemimartingale_quadraticVariation hF).complexIntegrandIntegral hF ha hr t ω +
        Complex.I * (2 *
          (hZ.1.isSemimartingale_quadraticCovariation hZ.2 hF).complexIntegrandIntegral
            hF ha hr t ω)) P := by
  filter_upwards [
    (hZ.1.isSemimartingale_quadraticVariation hF).complexIntegrandIntegral_sub_integrator
      (hZ.2.isSemimartingale_quadraticVariation hF) hF ha hr,
    IsSemimartingale.complexIntegrandIntegral_const_mul_integrator
      (hZ.1.isSemimartingale_quadraticCovariation hZ.2 hF) hF ha hr 2] with ω hs hm t
  have hh := congrArg₂ (fun a b : ℂ ↦ a + Complex.I * b) (hs t) (hm t)
  simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_ofNat] at hh
  convert hh using 1
  simp only [stochasticIntegral, quadraticVariation, complexProcess, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem IsComplexSemimartingale.stochasticIntegral_continuousQuadraticVariation_coordinates
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hZ.isComplexSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
        hF ha hr)
      (fun t ω ↦
        (hZ.1.isSemimartingale_continuousQuadraticVariation hF).complexIntegrandIntegral
          hF ha hr t ω -
        (hZ.2.isSemimartingale_continuousQuadraticVariation hF).complexIntegrandIntegral
          hF ha hr t ω +
        Complex.I * (2 *
          (hZ.1.isSemimartingale_continuousQuadraticCovariation hZ.2 hF).complexIntegrandIntegral
            hF ha hr t ω)) P := by
  filter_upwards [
    IsSemimartingale.complexIntegrandIntegral_sub_integrator
      (hZ.1.isSemimartingale_continuousQuadraticVariation hF)
      (hZ.2.isSemimartingale_continuousQuadraticVariation hF) hF ha hr,
    IsSemimartingale.complexIntegrandIntegral_const_mul_integrator
      (hZ.1.isSemimartingale_continuousQuadraticCovariation hZ.2 hF) hF ha hr 2]
      with ω hs hm t
  have hh := congrArg₂ (fun a b : ℂ ↦ a + Complex.I * b) (hs t) (hm t)
  simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_ofNat] at hh
  convert hh using 1
  simp only [stochasticIntegral, continuousQuadraticVariation, complexProcess, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

end ProbabilityTheory
