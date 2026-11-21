/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousFVSubstitution
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialIncrement
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrationByParts

/-! # Multiplication by a C1 function of a continuous FV clock

The integral against the semimartingale already contains the initial product.
The two left-limit initial corrections and the raw bracket's initial value
cancel against the initial term in FV substitution. No zero-starting assumption
on the semimartingale or the multiplier is needed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.contDiff_clock_mul_eq_integrals
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Q X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}
    (hQ : IsSemimartingale Q F P) (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (hcX : HasContinuousPaths X P) (h0 : Q 0 =ᵐ[P] 0) (hf : ContDiff ℝ 1 f) :
    let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
      fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hf.continuous
    let haD : Adapted F (fun t ω ↦ deriv f (Q t ω)) :=
      fun t ↦ hf.continuous_deriv_one.measurable.comp (hQ.adapted t)
    let hrD := hcQ.hasCagladPaths.continuous_comp hf.continuous_deriv_one
    Indistinguishable (fun t ω ↦ f (Q t ω) * X t ω)
      (fun t ω ↦ hX.stochasticIntegral hF haA hrA t ω +
        hQ.stochasticIntegral hF (fun r ↦ (hX.adapted r).mul (haD r))
          (hcX.hasCagladPaths.mul hrD) t ω) P := by
  let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
    fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
  let hA := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hv hcQ hf
  have hcA : HasContinuousPaths (fun t ω ↦ f (Q t ω)) P :=
    hcQ.mono fun _ h ↦ hf.continuous.comp h
  have hvA : HasFiniteVariationPaths (fun t ω ↦ f (Q t ω)) P :=
    hv.contDiff_comp hcQ hf
  filter_upwards [hA.integrationByParts hX hF,
    hA.quadraticCovariation_initial_of_continuous_finiteVariation_left hX hF hcA hvA,
    hX.stochasticIntegral_leftLimit_of_continuous hF haA hcA,
    hA.stochasticIntegral_leftLimit_of_continuous hF hX.adapted hcX,
    hQ.stochasticIntegral_contDiff_integrator_of_continuous_finiteVariation
      hF hv hcQ h0 hf hX.adapted hcX.hasCagladPaths, h0]
      with ω hp hq hx ha hs hz t
  have hp' := hp t
  simp only [Pi.mul_apply, Pi.add_apply, hq t, hx t, ha t, hs t] at hp'
  simp only [Pi.zero_apply] at hz
  rw [hz] at hp'
  linarith

end ProbabilityTheory
