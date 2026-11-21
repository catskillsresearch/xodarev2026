/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.ContinuousBracket
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationPreservation
public import StochLean.ForMathlib.VariationAlgebra

/-! # The finite-variation residual in the cadlag Ito formula

Removing the first-derivative stochastic integral leaves an actual locally
FV process, including its arbitrary initial constant and jump correction.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.hasFiniteVariationPaths_contDiff_sub_derivativeIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
    let ha : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
      fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
    let hr := hX.hasCadlagPaths.continuous_comp hd.continuous
    HasFiniteVariationPaths ((fun t ω ↦ f (X t ω)) -
      hX.stochasticIntegral hF (ha.leftLimitProcess_of_usual hF hr)
        hr.hasCagladPaths_leftLimitProcess) P := by
  dsimp only
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
  let hr := hX.hasCadlagPaths.continuous_comp hd.continuous
  let J := hX.stochasticIntegral hF (ha.leftLimitProcess_of_usual hF hr)
    hr.hasCagladPaths_leftLimitProcess
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
    fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
  let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
  let hC := hX.isSemimartingale_continuousQuadraticVariation hF
  have hvJ := hC.hasFiniteVariationPaths_stochasticIntegral hF
      (hX.hasFiniteVariationPaths_continuousQuadraticVariation hF)
      (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess
  filter_upwards [hX.ito_continuous_bracket hF hf, hvJ,
    hX.hasFiniteVariationPaths_contDiff_jump_remainders hF hf] with ω hi hvJω hvR
  have hvhalf := (lipschitzWith_smul (β := ℝ) (1 / 2 : ℝ)).comp_locallyBoundedVariationOn hvJω
  have hvC : LocallyBoundedVariationOn (fun _ : ℝ≥0 ↦ f (X 0 ω)) univ :=
    (monotone_const.monotoneOn univ).locallyBoundedVariationOn
  have hv := locallyBoundedVariationOn_add (locallyBoundedVariationOn_add hvC hvhalf) hvR
  have he : (fun t ↦ f (X t ω) - J t ω) =
      fun t ↦ f (X 0 ω) + (1 / 2 : ℝ) *
        (hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF
          (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess t ω +
        ∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω) := by
    funext t
    have h := hi t
    dsimp only [J]
    change _ = _ + (1 / 2 : ℝ) * _ + _ at h
    linarith only [h]
  change LocallyBoundedVariationOn (fun t ↦ f (X t ω) - J t ω) univ
  rw [he]
  exact hv

end ProbabilityTheory
