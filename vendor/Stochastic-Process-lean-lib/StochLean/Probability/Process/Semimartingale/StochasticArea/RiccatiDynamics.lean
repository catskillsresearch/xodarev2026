/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.LevyAreaRiccati
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousFVChangeOfVariables

/-! # Actual stochastic-integral equations for the terminal Riccati coefficients

The C1 finite-variation formula supplies the equations along any continuous
zero-starting FV clock, including the existing continuous bracket. The
derivative expressions are proved from the hyperbolic functions, not premises.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Q : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_levyAreaAlpha_drift
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Q P) (hc : HasContinuousPaths Q P)
    (h0 : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let ha : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2) :=
      fun t ↦ ((hα.continuous.measurable.comp (hQ.adapted t)).pow_const 2).sub measurable_const
    let hr := hc.hasCagladPaths.continuous_comp
      ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2)))
    Indistinguishable (hQ.stochasticIntegral hF ha hr)
      (fun t ω ↦ levyAreaAlpha u T (Q t ω) - levyAreaAlpha u T 0) P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let ha : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2) :=
    fun t ↦ ((hα.continuous.measurable.comp (hQ.adapted t)).pow_const 2).sub measurable_const
  let hr := hc.hasCagladPaths.continuous_comp
    ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2)))
  let haD : Adapted F (fun t ω ↦ deriv (levyAreaAlpha u T) (Q t ω)) :=
    fun t ↦ hα.continuous_deriv_one.measurable.comp (hQ.adapted t)
  let hrD := hc.hasCagladPaths.continuous_comp hα.continuous_deriv_one
  have he : Indistinguishable (fun t ω ↦ deriv (levyAreaAlpha u T) (Q t ω))
      (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2) P :=
    Eventually.of_forall fun ω t ↦ (hasDerivAt_levyAreaAlpha u T (Q t ω)).deriv
  exact (hQ.stochasticIntegral_congr_integrand hF haD hrD ha hr he).symm.trans
    (hQ.stochasticIntegral_derivative_of_continuous_finiteVariation hF hv hc h0 hα)

theorem IsSemimartingale.stochasticIntegral_levyAreaBeta_drift
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Q P) (hc : HasContinuousPaths Q P)
    (h0 : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let ha : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
      fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
    let hr := hc.hasCagladPaths.continuous_comp hα.continuous
    Indistinguishable (hQ.stochasticIntegral hF ha hr)
      (fun t ω ↦ levyAreaBeta u T (Q t ω) - levyAreaBeta u T 0) P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let hβ : ContDiff ℝ 1 (levyAreaBeta u T) := contDiff_levyAreaBeta u T
  let ha : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let hr := hc.hasCagladPaths.continuous_comp hα.continuous
  let haD : Adapted F (fun t ω ↦ deriv (levyAreaBeta u T) (Q t ω)) :=
    fun t ↦ hβ.continuous_deriv_one.measurable.comp (hQ.adapted t)
  let hrD := hc.hasCagladPaths.continuous_comp hβ.continuous_deriv_one
  have he : Indistinguishable (fun t ω ↦ deriv (levyAreaBeta u T) (Q t ω))
      (fun t ω ↦ levyAreaAlpha u T (Q t ω)) P :=
    Eventually.of_forall fun ω t ↦ (hasDerivAt_levyAreaBeta u T (Q t ω)).deriv
  exact (hQ.stochasticIntegral_congr_integrand hF haD hrD ha hr he).symm.trans
    (hQ.stochasticIntegral_derivative_of_continuous_finiteVariation hF hv hc h0 hβ)

end ProbabilityTheory
