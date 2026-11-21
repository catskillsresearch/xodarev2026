/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ConstantIntegrator

/-! # Complex integrands against a random constant real integrator

The real coordinate formulas retain the initial product. Neither the random
constant nor the initial integrand is required to be integrable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}

theorem complexIntegrandIntegral_const_initial
    (hZ : Measurable[F 0] Z) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable ((isSemimartingale_const_initial hZ).complexIntegrandIntegral hF ha hr)
      (fun _ ω ↦ H 0 ω * (Z ω : ℂ)) P := by
  filter_upwards [stochasticIntegral_const_initial hZ hF
      (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_re),
    stochasticIntegral_const_initial hZ hF
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im)] with ω hR hI t
  apply Complex.ext <;>
    simp [IsSemimartingale.complexIntegrandIntegral, complexProcess, hR t, hI t]

theorem complexIntegrandIntegral_const_initial_of_zero_initial_integrand
    (hZ : Measurable[F 0] Z) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (h0 : H 0 =ᵐ[P] 0) :
    Indistinguishable ((isSemimartingale_const_initial hZ).complexIntegrandIntegral hF ha hr)
      0 P := by
  filter_upwards [complexIntegrandIntegral_const_initial hZ hF ha hr, h0] with ω he hz t
  simp only [he t, hz, Pi.zero_apply, zero_mul]

end ProbabilityTheory
