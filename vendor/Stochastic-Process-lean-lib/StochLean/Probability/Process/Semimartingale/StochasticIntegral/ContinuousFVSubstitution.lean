/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousFVChangeOfVariables
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ConstantIntegrator
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Associativity
public import StochLean.Probability.Process.FiniteVariation.ChangeOfVariables

/-! # Integrating against C1 functions of a continuous FV clock

This is substitution for the actual Chapter II integral, retaining the
initial product `H_0 f(0)`. The clock starts at zero; the transformed clock
and the outer integrand need not start at zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticIntegral_contDiff_integrator_of_continuous_finiteVariation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Q H : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Q P) (hc : HasContinuousPaths Q P)
    (h0 : Q 0 =ᵐ[P] 0) (hf : ContDiff ℝ 1 f)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    let hY := isSemimartingale_contDiff_of_continuous_finiteVariation
      hQ.adapted hF hv hc hf
    let haD : Adapted F (fun t ω ↦ deriv f (Q t ω)) :=
      fun t ↦ hf.continuous_deriv_one.measurable.comp (hQ.adapted t)
    let hrD := hc.hasCagladPaths.continuous_comp hf.continuous_deriv_one
    Indistinguishable (hY.stochasticIntegral hF ha hr)
      (fun t ω ↦ H 0 ω * f 0 + hQ.stochasticIntegral hF
        (fun r ↦ (ha r).mul (haD r)) (hr.mul hrD) t ω) P := by
  let hY := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hv hc hf
  let haD : Adapted F (fun t ω ↦ deriv f (Q t ω)) :=
    fun t ↦ hf.continuous_deriv_one.measurable.comp (hQ.adapted t)
  let hrD := hc.hasCagladPaths.continuous_comp hf.continuous_deriv_one
  let hJ := hQ.isSemimartingale_stochasticIntegral hF haD hrD
  let hC := isSemimartingale_const_initial (P := P) (F := F)
    (Z := fun _ : Ω ↦ f 0) measurable_const
  have he : Indistinguishable
      ((fun (_ : ℝ≥0) (_ : Ω) ↦ f 0) + hQ.stochasticIntegral hF haD hrD)
      (fun t ω ↦ f (Q t ω)) P := by
    filter_upwards [hQ.stochasticIntegral_derivative_of_continuous_finiteVariation hF hv hc h0 hf]
      with ω hω t
    change f 0 + hQ.stochasticIntegral hF haD hrD t ω = f (Q t ω)
    rw [hω t]
    ring
  filter_upwards [hY.stochasticIntegral_congr_integrator (hC.add hJ) hF ha hr he.symm,
    hC.stochasticIntegral_add_integrator hJ hF ha hr,
    stochasticIntegral_const_initial (Z := fun _ : Ω ↦ f 0) measurable_const hF ha hr,
    hQ.stochasticIntegral_stochasticIntegral hF ha hr haD hrD]
      with ω heω hs hconst hassoc t
  rw [heω t, hs t]
  simp only [Pi.add_apply, hconst t, hassoc t]

end ProbabilityTheory
