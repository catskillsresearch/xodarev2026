/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.RawBracket
public import StochLean.Probability.Process.Semimartingale.Ito.Preservation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.IntegralDecomposition
public import StochLean.Probability.Process.Path.LeftLimitCompositionPositive

/-! # Protter II.32: the continuous-bracket form of the cadlag Ito formula

The first-order jump correction is genuinely absolutely summable. Conversion
from the raw formula uses the integral's proved continuous/atomic decomposition,
not an assumed interchange of divergent series. Left-limit integrands start at
zero, so the displayed difference has no hidden initial integral contribution.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.ito_continuous_bracket
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
    let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
      fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
    let hr₁ := hX.hasCadlagPaths.continuous_comp hd.continuous
    let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
      fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
    let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
    Indistinguishable (fun t ω ↦ f (X t ω) - f (X 0 ω))
      (fun t ω ↦ hX.stochasticIntegral hF (ha₁.leftLimitProcess_of_usual hF hr₁)
          hr₁.hasCagladPaths_leftLimitProcess t ω +
        (1 / 2 : ℝ) *
          (hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF
            (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess t ω +
        ∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω)) P := by
  dsimp only
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
    fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
  let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
  let H := leftLimitProcess (fun t ω ↦ deriv (deriv f) (X t ω))
  have hD := hX.stochasticIntegral_quadraticVariation_continuous_jump_decomposition hF
    (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess
  have hS := hX.summable_abs_caglad_weighted_sq_jumps hF hr₂.hasCagladPaths_leftLimitProcess
  filter_upwards [hX.ito_raw_bracket hF hf, hD, hS,
    hX.summable_abs_contDiff_jump_remainders hF hf, hX.hasCadlagPaths]
      with ω hi hdω hs hr hx t
  have hW : Summable (fun s : Ioc 0 t ↦ H s ω * (jumpProcess X s ω) ^ 2) :=
    (hs t).of_abs
  have hR : Summable (fun s : Ioc 0 t ↦ f (X s ω) - f (leftLimitProcess X s ω) -
      deriv f (leftLimitProcess X s ω) * jumpProcess X s ω) := (hr t).of_abs
  have hseries : (∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
      deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
      deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)) =
      (∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω)) -
      (1 / 2 : ℝ) * ∑' s : Ioc 0 t, H s ω * (jumpProcess X s ω) ^ 2 := by
    calc
      _ = ∑' s : Ioc 0 t, ((f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω) -
          (1 / 2 : ℝ) * (H s ω * (jumpProcess X s ω) ^ 2)) := by
        apply tsum_congr
        intro s
        dsimp only [H]
        rw [hx.leftLimitProcess_continuous_comp_of_pos hd.continuous_deriv_one s.2.1]
        ring
      _ = _ := (hR.tsum_sub (hW.mul_left (1 / 2 : ℝ))).trans
        (congrArg (fun z ↦ _ - z) (hW.tsum_mul_left (1 / 2 : ℝ)))
  have hd' := hdω t
  simp only [leftLimitProcess_zero, Pi.zero_apply, zero_mul, zero_add] at hd'
  have hi' := hi t
  rw [hseries] at hi'
  change _ = _ + (1 / 2 : ℝ) * _ + _ at hi'
  dsimp only [H] at hi'
  linarith only [hi', hd']

end ProbabilityTheory
