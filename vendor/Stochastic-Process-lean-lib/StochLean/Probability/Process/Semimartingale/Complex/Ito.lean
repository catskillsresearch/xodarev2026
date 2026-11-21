/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.ItoComponent

/-! # Protter II.36: complex analytic Ito calculus for cadlag semimartingales

The formula uses the canonical complex bilinear continuous bracket and the
actual absolutely convergent first-order jump correction. The common event
covers every finite time and both real coordinates simultaneously.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ} {f : ℂ → ℂ}

theorem IsComplexSemimartingale.ito_continuous_bracket
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (hf : Differentiable ℂ f) :
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
        (1 / 2 : ℝ) •
          (hZ.isComplexSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
            hF (Adapted.complexLeftLimitProcess_of_usual ha₂ hF hr₂)
            hr₂.hasCagladPaths_complexLeftLimitProcess t ω +
        ∑' s : Ioc 0 t, (f (Z s ω) - f (complexLeftLimitProcess Z s ω) -
          deriv f (complexLeftLimitProcess Z s ω) * complexJumpProcess Z s ω)) P := by
  dsimp only
  filter_upwards [hZ.ito_continuous_bracket_component hF hf Complex.reCLM,
    hZ.ito_continuous_bracket_component hF hf Complex.imCLM] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

theorem IsComplexSemimartingale.ito_continuous_bracket_of_continuous
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
        (1 / 2 : ℝ) •
          (hZ.isComplexSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
            hF (Adapted.complexLeftLimitProcess_of_usual ha₂ hF hr₂)
            hr₂.hasCagladPaths_complexLeftLimitProcess t ω) P := by
  dsimp only
  filter_upwards [hZ.ito_continuous_bracket hF hf, hc] with ω hi hcω t
  have hj (s : Ioc 0 t) : complexJumpProcess Z s ω = 0 :=
    hcω.complexJumpProcess_eq_zero (ne_of_gt s.2.1)
  have hl (s : Ioc 0 t) : complexLeftLimitProcess Z s ω = Z s ω :=
    (sub_eq_zero.mp (hj s)).symm
  simpa only [hl, hj, sub_self, mul_zero, sub_zero, tsum_zero, add_zero] using hi t

end ProbabilityTheory
