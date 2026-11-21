/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.FiskStratonovich.Basic
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump

/-! # The Fisk--Stratonovich correction vanishes with a finite-variation argument

This includes discontinuous finite-variation paths: only continuous
covariation enters the correction, not the raw bracket or jump products.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.fiskStratonovichIntegral_eq_stochasticIntegral_of_finiteVariation_integrand
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Y P) :
    Indistinguishable (hX.fiskStratonovichIntegral hY hF)
      (hX.stochasticIntegral hF
        (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess) P := by
  filter_upwards [hY.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hX hF
    (hY.isQuadraticPureJump_of_finiteVariation hF hv)] with ω hz t
  simp only [fiskStratonovichIntegral, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hz t, Pi.zero_apply, mul_zero, add_zero]

theorem
    IsSemimartingale.fiskStratonovichIntegral_eq_stochasticIntegral_of_finiteVariation_integrator
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.fiskStratonovichIntegral hY hF)
      (hX.stochasticIntegral hF
        (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess) P := by
  filter_upwards [hY.continuousQuadraticCovariation_zero_of_quadraticPureJump_right hX hF
    (hX.isQuadraticPureJump_of_finiteVariation hF hv)] with ω hz t
  simp only [fiskStratonovichIntegral, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hz t, Pi.zero_apply, mul_zero, add_zero]

end ProbabilityTheory
