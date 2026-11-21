/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ZeroIntegrator

/-! # Complex-valued integration against a zero real integrator -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.complexIntegrandIntegral_eq_zero_of_integrator_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hz : Indistinguishable X 0 P) :
    Indistinguishable (hX.complexIntegrandIntegral hF ha hr) 0 P := by
  filter_upwards [hX.stochasticIntegral_eq_zero_of_integrator_eq_zero hF
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re) hz,
    hX.stochasticIntegral_eq_zero_of_integrator_eq_zero hF
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im) hz] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

end ProbabilityTheory
