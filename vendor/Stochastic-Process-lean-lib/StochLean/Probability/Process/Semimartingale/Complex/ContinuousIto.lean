/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Ito
public import StochLean.Probability.Process.Semimartingale.Complex.ContinuousBracketIntegral

/-! # Protter II.35: analytic Ito formula for continuous complex semimartingales

This is the source raw-bilinear-bracket formula. The source left-limit
integrands vanish at zero, so the initial square is removed by a proved
integral comparison; the raw bracket itself is not redefined to start at zero.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsComplexSemimartingale.ito_of_continuous
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ} {f : ℂ → ℂ}
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths Z P) (hf : Differentiable ℂ f) :
    let ha₁ : Adapted F (fun t ω ↦ deriv f (Z t ω)) :=
      fun t ↦ hf.deriv.continuous.measurable.comp (hZ.adapted t)
    let hr₁ := hZ.hasCadlagPaths.continuous_comp hf.deriv.continuous
    let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (Z t ω)) :=
      fun t ↦ hf.deriv.deriv.continuous.measurable.comp (hZ.adapted t)
    let hr₂ := hZ.hasCadlagPaths.continuous_comp hf.deriv.deriv.continuous
    Indistinguishable (fun t ω ↦ f (Z t ω) - f (Z 0 ω))
      (fun t ω ↦ hZ.stochasticIntegral hF
          (Adapted.complexLeftLimitProcess_of_usual ha₁ hF hr₁)
          hr₁.hasCagladPaths_complexLeftLimitProcess t ω +
        (1 / 2 : ℝ) • (hZ.isComplexSemimartingale_quadraticVariation hF).stochasticIntegral
          hF (Adapted.complexLeftLimitProcess_of_usual ha₂ hF hr₂)
          hr₂.hasCagladPaths_complexLeftLimitProcess t ω) P := by
  dsimp only
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (Z t ω)) :=
    fun t ↦ hf.deriv.deriv.continuous.measurable.comp (hZ.adapted t)
  let hr₂ := hZ.hasCadlagPaths.continuous_comp hf.deriv.deriv.continuous
  have h0 : complexLeftLimitProcess (fun t ω ↦ deriv (deriv f) (Z t ω)) 0 =ᵐ[P] 0 :=
    Filter.Eventually.of_forall (fun ω ↦ congrFun (complexLeftLimitProcess_zero _) ω)
  filter_upwards [hZ.ito_continuous_bracket_of_continuous hF hc hf,
    hZ.stochasticIntegral_raw_continuous_bracket_of_continuous hF hc
      (Adapted.complexLeftLimitProcess_of_usual ha₂ hF hr₂)
      hr₂.hasCagladPaths_complexLeftLimitProcess h0] with ω hi hq t
  rw [hq t]
  exact hi t

end ProbabilityTheory
