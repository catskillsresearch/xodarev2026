/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Continuous
public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Congr
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift

/-! # Protter II.38: the continuous stochastic-exponential inverse

The continuous-bracket formula allows arbitrary random initial values.
The source raw-bracket formula requires zero initial value. These are
identities for the existing product-defined stochastic exponentials.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticExponential_inv_continuous_bracket
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    let hY := (hX.const_mul (-1)).add (hX.isSemimartingale_continuousQuadraticVariation hF)
    Indistinguishable (fun t ω ↦ (hX.stochasticExponential hF t ω)⁻¹)
      (hY.stochasticExponential hF) P := by
  dsimp only
  let Q := hX.continuousQuadraticVariation hF
  let Y := (fun t ω ↦ (-1 : ℝ) * X t ω) + Q
  let hQ := hX.isSemimartingale_continuousQuadraticVariation hF
  have hY : IsSemimartingale Y F P := (hX.const_mul (-1)).add hQ
  have hcY : HasContinuousPaths Y P := hc.mono (fun ω hx ↦
    (hx.const_mul (-1)).add (hX.continuous_continuousQuadraticVariation hF ω))
  have hq := (hX.const_mul (-1)).continuousQuadraticVariation_add_finiteVariation hQ hF
    (hX.hasFiniteVariationPaths_continuousQuadraticVariation hF)
  filter_upwards [hX.stochasticExponential_of_continuous hF hc,
    hY.stochasticExponential_of_continuous hF hcY, hq,
    hX.continuousQuadraticVariation_const_mul hF (-1)] with ω hx hy hqω hscale t
  have he : Y t ω - (1 / 2 : ℝ) * hY.continuousQuadraticVariation hF t ω =
      -(X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω) := by
    rw [hqω t, hscale t]
    simp only [Y, Q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hx t, hy t, he, Real.exp_neg]

theorem IsSemimartingale.stochasticExponential_inv_raw_bracket
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (h0 : X 0 =ᵐ[P] 0) :
    let hY := (hX.const_mul (-1)).add (hX.isSemimartingale_quadraticVariation hF)
    Indistinguishable (fun t ω ↦ (hX.stochasticExponential hF t ω)⁻¹)
      (hY.stochasticExponential hF) P := by
  dsimp only
  let hR := (hX.const_mul (-1)).add (hX.isSemimartingale_quadraticVariation hF)
  let hC := (hX.const_mul (-1)).add (hX.isSemimartingale_continuousQuadraticVariation hF)
  have he : Indistinguishable
      ((fun t ω ↦ (-1 : ℝ) * X t ω) + hX.quadraticVariation hF)
      ((fun t ω ↦ (-1 : ℝ) * X t ω) + hX.continuousQuadraticVariation hF) P := by
    filter_upwards [hX.continuousQuadraticVariation_eq_of_continuous hF hc, h0]
      with ω hq hz t
    simp only [Pi.add_apply, hq t, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      sub_zero]
  exact (hX.stochasticExponential_inv_continuous_bracket hF hc).trans
    (hR.stochasticExponential_congr hC hF he).symm

end ProbabilityTheory
