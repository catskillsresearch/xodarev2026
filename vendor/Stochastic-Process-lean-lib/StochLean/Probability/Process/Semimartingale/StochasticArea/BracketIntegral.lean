/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.ExponentBracket
public import StochLean.Probability.Process.Semimartingale.Complex.Invariance
public import StochLean.Probability.Process.Semimartingale.Complex.Associativity

/-! # Integrating the actual compensated-area-exponent bracket

The proved complex bracket is a real-valued stochastic integral. Version
invariance and associativity reduce its integral to the existing clock owner.
The outer integrand need not start at zero.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticIntegral_continuousQuadraticVariation_stochasticAreaExponent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
      fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
    let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
      fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
    let hrR : HasCagladPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
      simpa only [pow_two, Pi.mul_def, Pi.add_def] using
        (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
          (hcY.hasCagladPaths.mul hcY.hasCagladPaths)
    let haD : Adapted F (fun t ω ↦ (X t ω ^ 2 + Y t ω ^ 2) *
        (levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2)) :=
      fun t ↦ (haR t).mul (((haA t).pow_const 2).sub measurable_const)
    let hrD := hrR.mul (hcQ.hasCagladPaths.continuous_comp
      ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2))))
    let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
    let hB := hK.isComplexSemimartingale_continuousQuadraticVariation hF
    Indistinguishable (hB.stochasticIntegral hF ha hr)
      (hQ.complexIntegrandIntegral hF
        (fun t ↦ (ha t).mul (Complex.continuous_ofReal.measurable.comp (haD t)))
        (hr.mul (hrD.continuous_comp Complex.continuous_ofReal))) P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
    fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
  let hrR : HasCagladPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
    simpa only [pow_two, Pi.mul_def, Pi.add_def] using
      (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
        (hcY.hasCagladPaths.mul hcY.hasCagladPaths)
  let haD : Adapted F (fun t ω ↦ (X t ω ^ 2 + Y t ω ^ 2) *
      (levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2)) :=
    fun t ↦ (haR t).mul (((haA t).pow_const 2).sub measurable_const)
  let hrD := hrR.mul (hcQ.hasCagladPaths.continuous_comp
    ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2))))
  let hK := hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T
  let hB := hK.isComplexSemimartingale_continuousQuadraticVariation hF
  let hJ := hQ.isSemimartingale_stochasticIntegral hF haD hrD
  have he := hX.continuousQuadraticVariation_stochasticAreaExponent hY hQ hF
    hqX hqY ho hcX hcY hvQ hcQ h0X h0Y h0Q u T
  exact (hB.stochasticIntegral_of_indistinguishable_real_integrator hJ hF ha hr he).trans
    (hQ.complexIntegrandIntegral_stochasticIntegral hF ha hr haD hrD)

end ProbabilityTheory
