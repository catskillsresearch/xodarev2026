/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Basic
public import StochLean.Analysis.PathVariation.ExponentialJumpProductMultiplication
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Jump

/-! # Protter II.38: multiplication of stochastic exponentials

The proof uses the actual products and canonical brackets, not uniqueness
of a stochastic equation. For arbitrary initial values the raw bracket's
initial product contributes an explicit exponential factor. No nonvanishing
condition is imposed on either stochastic exponential.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticExponential_add_add_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    let hZ := (hX.add hY).add (hX.isSemimartingale_quadraticCovariation hY hF)
    Indistinguishable (hZ.stochasticExponential hF)
      (fun t ω ↦ Real.exp (X 0 ω * Y 0 ω) *
        hX.stochasticExponential hF t ω * hY.stochasticExponential hF t ω) P := by
  dsimp only
  let B := hX.quadraticCovariation hY hF
  let Z := X + Y + B
  let hB := hX.isSemimartingale_quadraticCovariation hY hF
  have hZ : IsSemimartingale Z F P := (hX.add hY).add hB
  have hQ := (hX.add hY).continuousQuadraticVariation_add_finiteVariation hB hF
    (hX.hasFiniteVariationPaths_quadraticCovariation hY hF)
  filter_upwards [hQ, hX.continuousQuadraticVariation_add hY hF,
    hX.quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.jumpProcess_quadraticCovariation hY hF, hX.hasCadlagPaths, hY.hasCadlagPaths,
    hB.hasCadlagPaths, hX.summable_sq_jumps hF, hY.summable_sq_jumps hF]
      with ω hQω hQa hd hjB hx hy hb hxs hys t
  have hjZ (s : ℝ≥0) : jumpProcess Z s ω =
      jumpProcess X s ω + jumpProcess Y s ω + jumpProcess X s ω * jumpProcess Y s ω := by
    rw [(hx.add hy).jumpProcess_add hb s, hx.jumpProcess_add hy s, hjB s]
  let C := ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω
  have hp : stochasticExponentialJumpProduct Z t ω =
      stochasticExponentialJumpProduct X t ω * stochasticExponentialJumpProduct Y t ω *
        Real.exp (-C) := by
    simp only [stochasticExponentialJumpProduct, hjZ]
    exact tprod_exponentialJumpFactor_add_add_mul (hxs t) (hys t) (hd t).1.of_abs
  have he : Z t ω - (1 / 2 : ℝ) * hZ.continuousQuadraticVariation hF t ω =
      (X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω) +
      (Y t ω - (1 / 2 : ℝ) * hY.continuousQuadraticVariation hF t ω) +
        X 0 ω * Y 0 ω + C := by
    rw [hQω t, hQa t]
    simp only [Z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hd' := (hd t).2
    change B t ω = X 0 ω * Y 0 ω + hX.continuousQuadraticCovariation hY hF t ω + C at hd'
    linarith only [hd']
  change Real.exp (Z t ω - (1 / 2 : ℝ) * hZ.continuousQuadraticVariation hF t ω) *
    stochasticExponentialJumpProduct Z t ω = _
  rw [he, hp]
  simp only [Real.exp_add, stochasticExponential]
  have hc : Real.exp C * Real.exp (-C) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = Real.exp (X 0 ω * Y 0 ω) *
        (Real.exp (X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω) *
          stochasticExponentialJumpProduct X t ω) *
        (Real.exp (Y t ω - (1 / 2 : ℝ) * hY.continuousQuadraticVariation hF t ω) *
          stochasticExponentialJumpProduct Y t ω) * (Real.exp C * Real.exp (-C)) := by ring
    _ = _ := by rw [hc, mul_one]

theorem IsSemimartingale.stochasticExponential_mul
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hX0 : X 0 =ᵐ[P] 0) (hY0 : Y 0 =ᵐ[P] 0) :
    let hZ := (hX.add hY).add (hX.isSemimartingale_quadraticCovariation hY hF)
    Indistinguishable (hX.stochasticExponential hF * hY.stochasticExponential hF)
      (hZ.stochasticExponential hF) P := by
  dsimp only
  filter_upwards [hX.stochasticExponential_add_add_quadraticCovariation hY hF, hX0, hY0]
    with ω he hx hy t
  simpa only [hx, hy, Pi.zero_apply, zero_mul, Real.exp_zero, one_mul, Pi.mul_apply]
    using (he t).symm

end ProbabilityTheory
