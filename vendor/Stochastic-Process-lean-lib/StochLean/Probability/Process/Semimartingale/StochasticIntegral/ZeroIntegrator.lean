/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance

/-! # Integration against an indistinguishably zero integrator -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticIntegral_eq_zero_of_integrator_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hz : Indistinguishable X 0 P) :
    Indistinguishable (hX.stochasticIntegral hF ha hr) 0 P := by
  have he : Indistinguishable X (fun t ω ↦ (0 : ℝ) * X t ω) P := by
    filter_upwards [hz] with ω hzω t
    simpa only [zero_mul, Pi.zero_apply] using hzω t
  filter_upwards [hX.stochasticIntegral_congr_integrator (hX.const_mul 0) hF ha hr he,
    hX.stochasticIntegral_const_mul_integrator hF ha hr 0] with ω heω hm t
  exact (heω t).trans ((hm t).trans (by simp only [Pi.smul_apply, smul_eq_mul, zero_mul,
    Pi.zero_apply]))

end ProbabilityTheory
