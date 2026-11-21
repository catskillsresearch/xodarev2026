/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousIntegral

/-! # The source Fisk--Stratonovich integral of semimartingales

The integrand is a semimartingale made left continuous by the source
left-limit operation. The correction uses continuous covariation only.
This is not an extension to arbitrary caglad integrands.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.fiskStratonovichIntegral
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ :=
  hX.stochasticIntegral hF
    (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
    hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess +
      (1 / 2 : ℝ) • hY.continuousQuadraticCovariation hX hF

theorem IsSemimartingale.fiskStratonovichIntegral_proof_irrel
    (hX hX' : IsSemimartingale X F P) (hY hY' : IsSemimartingale Y F P)
    (hF hF' : F.IsUsual P) :
    hX.fiskStratonovichIntegral hY hF = hX'.fiskStratonovichIntegral hY' hF' := rfl

theorem IsSemimartingale.isSemimartingale_fiskStratonovichIntegral
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.fiskStratonovichIntegral hY hF) F P :=
  (hX.isSemimartingale_stochasticIntegral hF
    (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
    hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess).add
      ((hY.isSemimartingale_continuousQuadraticCovariation hX hF).const_mul (1 / 2))

theorem IsSemimartingale.fiskStratonovichIntegral_zero_ae
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    hX.fiskStratonovichIntegral hY hF 0 =ᵐ[P] 0 := by
  filter_upwards [hX.stochasticIntegral_zero_ae hF
    (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
    hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess] with ω h0
  simp only [fiskStratonovichIntegral, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    h0, leftLimitProcess_zero, Pi.zero_apply, zero_mul,
    continuousQuadraticCovariation_zero, mul_zero, add_zero]

end ProbabilityTheory
