/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.RealExponentIntegral
public import StochLean.Probability.Process.Semimartingale.StochasticArea.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticArea.BracketIntegral
public import StochLean.Probability.Process.Semimartingale.Complex.ContinuousIto

/-! # Actual Ito cancellation for the compensated stochastic-area exponential

The real exponent integral and the actual complex bilinear bracket have
opposite half-clock terms. The analytic Ito formula cancels them. Only the
source left-limit integrand's proved zero initial value removes the initial
product; the exponent's own initial value is retained on the left.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticAreaExponential_sub_initial_eq_integrals
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    let hE := hX.isComplexSemimartingale_stochasticAreaExponential hY hQ hF u T
    let haL := Adapted.complexLeftLimitProcess_of_usual hE.adapted hF hE.hasCadlagPaths
    let hrL := hE.hasCadlagPaths.hasCagladPaths_complexLeftLimitProcess
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
      fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
    let haAX : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * X t ω) :=
      fun t ↦ (haA t).mul (hX.adapted t)
    let hrAX := hrA.mul hcX.hasCagladPaths
    let haAY : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * Y t ω) :=
      fun t ↦ (haA t).mul (hY.adapted t)
    let hrAY := hrA.mul hcY.hasCagladPaths
    Indistinguishable
      (fun t ω ↦ hX.stochasticAreaExponential hY hF Q u T t ω -
        hX.stochasticAreaExponential hY hF Q u T 0 ω)
      (fun t ω ↦
        -hX.complexIntegrandIntegral hF
          (fun r ↦ (haL r).mul (Complex.continuous_ofReal.measurable.comp (haAX r)))
          (hrL.mul (hrAX.continuous_comp Complex.continuous_ofReal)) t ω -
        hY.complexIntegrandIntegral hF
          (fun r ↦ (haL r).mul (Complex.continuous_ofReal.measurable.comp (haAY r)))
          (hrL.mul (hrAY.continuous_comp Complex.continuous_ofReal)) t ω +
        Complex.I * (u : ℂ) *
          (hY.complexIntegrandIntegral hF
            (fun r ↦ (haL r).mul (Complex.continuous_ofReal.measurable.comp (hX.adapted r)))
            (hrL.mul (hcX.hasCagladPaths.continuous_comp Complex.continuous_ofReal)) t ω -
          hX.complexIntegrandIntegral hF
            (fun r ↦ (haL r).mul (Complex.continuous_ofReal.measurable.comp (hY.adapted r)))
            (hrL.mul (hcY.hasCagladPaths.continuous_comp Complex.continuous_ofReal)) t ω)) P := by
  let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
  let hE := hX.isComplexSemimartingale_stochasticAreaExponential hY hQ hF u T
  let haL := Adapted.complexLeftLimitProcess_of_usual hE.adapted hF hE.hasCadlagPaths
  let hrL := hE.hasCadlagPaths.hasCagladPaths_complexLeftLimitProcess
  let hArea := hX.isSemimartingale_stochasticArea hY hF
  let hImag := hArea.const_mul u
  let hBK := hK.isComplexSemimartingale_continuousQuadraticVariation hF
  have hi := hK.ito_continuous_bracket_of_continuous hF
    (hX.hasContinuousPaths_stochasticAreaExponent hY hF hcX hcY hcQ u T)
    Complex.differentiable_exp
  have hd : deriv Complex.exp = Complex.exp := by
    funext z
    simp
  simp only [hd] at hi
  have hR := hX.complexIntegrandIntegral_stochasticAreaExponent_re hY hQ hF hqX hqY
    hcX hcY hvQ hcQ h0X h0Y h0Q u T haL hrL
  have hA := hX.complexIntegrandIntegral_stochasticArea hY hF hcX hcY haL hrL
  have hB := hX.stochasticIntegral_continuousQuadraticVariation_stochasticAreaExponent
    hY hQ hF hqX hqY ho hcX hcY hvQ hcQ h0X h0Y h0Q u T haL hrL
  filter_upwards [hi, hR, hArea.complexIntegrandIntegral_const_mul_integrator hF haL hrL u,
    hA, hB] with ω hiω hr hs ha hb t
  have h := hiω t
  change hX.stochasticAreaExponential hY hF Q u T t ω -
    hX.stochasticAreaExponential hY hF Q u T 0 ω =
      hK.stochasticIntegral hF haL hrL t ω +
        (1 / 2 : ℝ) • hBK.stochasticIntegral hF haL hrL t ω at h
  have hfirst : hK.stochasticIntegral hF haL hrL t ω =
      hK.1.complexIntegrandIntegral hF haL hrL t ω +
        Complex.I * hImag.complexIntegrandIntegral hF haL hrL t ω := rfl
  rw [hfirst, hr t, hs t, hb t] at h
  simp only [Pi.smul_apply, Complex.real_smul] at h
  rw [ha t] at h
  simp only [complexLeftLimitProcess_zero, Pi.zero_apply, zero_mul,
    Pi.sub_apply, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at h
  exact h.trans (by ring)

end ProbabilityTheory
