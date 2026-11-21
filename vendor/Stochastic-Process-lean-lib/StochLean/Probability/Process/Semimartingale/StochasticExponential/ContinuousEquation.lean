/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Continuous
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift
public import StochLean.Probability.Process.Semimartingale.Ito.ContinuousBracket
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance

/-! # The stochastic-exponential integral equation for continuous integrators

Ito's formula cancels the canonical continuous quadratic variation drift.
The equation is proved for the product-defined process, not used to define
an unproved solution. The arbitrary initial value is retained explicitly.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticExponential_sub_initial_eq_integral_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    let hE := hX.isSemimartingale_stochasticExponential_of_continuous hF hc
    Indistinguishable
      (fun t ω ↦ hX.stochasticExponential hF t ω - Real.exp (X 0 ω))
      (hX.stochasticIntegral hF
        (hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths)
        hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess) P := by
  dsimp only
  let K : ℝ≥0 → Ω → ℝ := fun t ω ↦
    X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω
  let hQ := hX.isSemimartingale_continuousQuadraticVariation hF
  let hA := hQ.const_mul (1 / 2)
  have hK : IsSemimartingale K F P := hX.sub hA
  have hvA : HasFiniteVariationPaths
      (fun t ω ↦ (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω) P := by
    apply Filter.Eventually.of_forall
    intro ω
    have hm : Monotone (fun t ↦ (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω) :=
      fun _ _ hst ↦ mul_le_mul_of_nonneg_left
        (hX.monotone_continuousQuadraticVariation hF ω hst) (by norm_num)
    exact (hm.monotoneOn univ).locallyBoundedVariationOn
  have hcK : HasContinuousPaths K P := hc.mono (fun ω h ↦
    h.sub ((hX.continuous_continuousQuadraticVariation hF ω).const_mul (1 / 2)))
  let haG : Adapted F (fun t ω ↦ Real.exp (K t ω)) :=
    fun t ↦ Real.continuous_exp.measurable.comp (hK.adapted t)
  let hrG := hK.hasCadlagPaths.continuous_comp Real.continuous_exp
  let haL := haG.leftLimitProcess_of_usual hF hrG
  let hrL := hrG.hasCagladPaths_leftLimitProcess
  have hbr := hX.continuousQuadraticVariation_sub_finiteVariation hA hF hvA
  have hJbr := IsSemimartingale.stochasticIntegral_congr_integrator
    (hK.isSemimartingale_continuousQuadraticVariation hF) hQ hF haL hrL hbr
  let hE := hX.isSemimartingale_stochasticExponential_of_continuous hF hc
  have he := hX.stochasticExponential_of_continuous hF hc
  have hJ := hX.stochasticIntegral_congr_integrand hF
    (hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths)
    hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess haL hrL he.leftLimitProcess
  have hi := hK.ito_continuous_bracket hF Real.contDiff_exp
  have hd : deriv Real.exp = Real.exp := Real.deriv_exp
  simp only [hd] at hi
  filter_upwards [hi, hcK, hX.stochasticIntegral_sub_integrator hA hF haL hrL,
    hQ.stochasticIntegral_const_mul_integrator hF haL hrL (1 / 2), hJbr, he, hJ]
      with ω hiω hcω hsub hscale hbrω heω hJω t
  have hj (s : Ioc 0 t) : Real.exp (K s ω) - Real.exp (leftLimitProcess K s ω) -
      Real.exp (leftLimitProcess K s ω) * jumpProcess K s ω = 0 := by
    rw [hcω.leftLimitProcess_eq (ne_of_gt s.2.1), hcω.jumpProcess_eq_zero (ne_of_gt s.2.1)]
    ring
  have hform := hiω t
  simp only [hj, tsum_zero, add_zero] at hform
  rw [hsub t, hbrω t] at hform
  simp only [Pi.sub_apply, hscale t, Pi.smul_apply, smul_eq_mul] at hform
  have hinit : Real.exp (K 0 ω) = Real.exp (X 0 ω) := by
    simp only [K, continuousQuadraticVariation_zero, mul_zero, sub_zero]
  rw [hinit] at hform
  rw [heω t, hJω t]
  exact hform.trans (by ring)

theorem IsSemimartingale.stochasticExponential_eq_one_add_integral_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (h0 : X 0 =ᵐ[P] 0) :
    let hE := hX.isSemimartingale_stochasticExponential_of_continuous hF hc
    Indistinguishable (hX.stochasticExponential hF)
      (fun t ω ↦ 1 + hX.stochasticIntegral hF
        (hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths)
        hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess t ω) P := by
  dsimp only
  filter_upwards [hX.stochasticExponential_sub_initial_eq_integral_of_continuous hF hc, h0]
    with ω hi hz t
  have h := hi t
  simp only [hz, Pi.zero_apply, Real.exp_zero] at h
  linarith only [h]

end ProbabilityTheory
