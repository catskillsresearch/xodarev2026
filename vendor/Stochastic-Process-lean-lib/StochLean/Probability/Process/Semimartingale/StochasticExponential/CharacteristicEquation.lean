/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Characteristic
public import StochLean.Probability.Process.Semimartingale.Complex.ContinuousIto
public import StochLean.Probability.Process.Semimartingale.Complex.ZeroIntegrator
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump

/-! # The compensated characteristic exponential solves its integral equation

For continuous real integrators the positive real compensation cancels the
negative imaginary-imaginary bilinear bracket. All integrals are the existing
real coordinate integrals; initial values need not be zero or integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.characteristicExponential_sub_initial_eq_integral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) (u : ℝ) :
    let hE := hX.isComplexSemimartingale_characteristicExponential hF u
    let haL := Adapted.complexLeftLimitProcess_of_usual hE.adapted hF hE.hasCadlagPaths
    let hrL := hE.hasCadlagPaths.hasCagladPaths_complexLeftLimitProcess
    Indistinguishable
      (fun t ω ↦ hX.characteristicExponential hF u t ω -
        hX.characteristicExponential hF u 0 ω)
      (fun t ω ↦ Complex.I * (u : ℂ) * hX.complexIntegrandIntegral hF haL hrL t ω) P := by
  dsimp only
  let Q := hX.continuousQuadraticVariation hF
  let U := fun t ω ↦ ((1 / 2 : ℝ) * u ^ 2) * Q t ω
  let V := fun t ω ↦ u * X t ω
  let hQ := hX.isSemimartingale_continuousQuadraticVariation hF
  let hU := hQ.const_mul ((1 / 2) * u ^ 2)
  let hV := hX.const_mul u
  let hK := hX.isComplexSemimartingale_characteristicExponent hF u
  let hE := hX.isComplexSemimartingale_characteristicExponential hF u
  let haL := Adapted.complexLeftLimitProcess_of_usual hE.adapted hF hE.hasCadlagPaths
  let hrL := hE.hasCadlagPaths.hasCagladPaths_complexLeftLimitProcess
  have hvU : HasFiniteVariationPaths U P := by
    apply Filter.Eventually.of_forall
    intro ω
    have hm : Monotone (U · ω) := fun _ _ hst ↦ mul_le_mul_of_nonneg_left
      (hX.monotone_continuousQuadraticVariation hF ω hst) (by positivity)
    exact (hm.monotoneOn univ).locallyBoundedVariationOn
  have hzeroU := hU.isQuadraticPureJump_of_finiteVariation hF hvU
  have h00 := IsSemimartingale.complexIntegrandIntegral_eq_zero_of_integrator_eq_zero
    (hU.isSemimartingale_continuousQuadraticVariation hF) hF haL hrL hzeroU
  have h01 := IsSemimartingale.complexIntegrandIntegral_eq_zero_of_integrator_eq_zero
    (hU.isSemimartingale_continuousQuadraticCovariation hV hF) hF haL hrL
    (hU.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hV hF hzeroU)
  have hvq : Indistinguishable (hV.continuousQuadraticVariation hF)
      (fun t ω ↦ u ^ 2 * Q t ω) P := hX.continuousQuadraticVariation_const_mul hF u
  have h11 := IsSemimartingale.complexIntegrandIntegral_congr_integrator
    (hV.isSemimartingale_continuousQuadraticVariation hF) (hQ.const_mul (u ^ 2))
    hF haL hrL hvq
  have hi := hK.ito_continuous_bracket_of_continuous hF
    (hX.hasContinuousPaths_characteristicExponent hF hc u) Complex.differentiable_exp
  have hd : deriv Complex.exp = Complex.exp := by funext z; simp
  simp only [hd] at hi
  have hcoord := hK.stochasticIntegral_continuousQuadraticVariation_coordinates hF haL hrL
  change Indistinguishable
    ((hK.isComplexSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF haL hrL)
    (fun t ω ↦ (hU.isSemimartingale_continuousQuadraticVariation hF).complexIntegrandIntegral
        hF haL hrL t ω -
      (hV.isSemimartingale_continuousQuadraticVariation hF).complexIntegrandIntegral
        hF haL hrL t ω +
      Complex.I * (2 * IsSemimartingale.complexIntegrandIntegral
        (hU.isSemimartingale_continuousQuadraticCovariation hV hF)
        hF haL hrL t ω)) P at hcoord
  filter_upwards [hi, hcoord,
    h00, h01, h11, hQ.complexIntegrandIntegral_const_mul_integrator hF haL hrL (u ^ 2),
    hQ.complexIntegrandIntegral_const_mul_integrator hF haL hrL ((1 / 2) * u ^ 2),
    hX.complexIntegrandIntegral_const_mul_integrator hF haL hrL u]
      with ω hiω hcoords h00ω h01ω h11ω hsq hhalf hu t
  have h := hiω t
  change hX.characteristicExponential hF u t ω -
    hX.characteristicExponential hF u 0 ω = hK.stochasticIntegral hF haL hrL t ω +
      (1 / 2 : ℝ) • (hK.isComplexSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
        hF haL hrL t ω at h
  have hfirst : hK.stochasticIntegral hF haL hrL t ω =
      hU.complexIntegrandIntegral hF haL hrL t ω +
        Complex.I * hV.complexIntegrandIntegral hF haL hrL t ω := rfl
  rw [hfirst, hcoords t, h00ω t, h01ω t, h11ω t, hsq t, hhalf t, hu t] at h
  simp only [Pi.zero_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow] at h
  exact h.trans (by ring)

end ProbabilityTheory
