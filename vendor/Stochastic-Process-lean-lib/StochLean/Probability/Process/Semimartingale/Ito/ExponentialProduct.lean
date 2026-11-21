/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.VectorContinuousBracket
public import StochLean.ForMathlib.Analysis.ExponentialProductCoordinates
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ZeroIntegrator

/-! # Ito's formula for an exponential times a finite-variation factor

This is the actual two-coordinate formula. The finite-variation factor need
not be positive or nonzero. Its continuous mixed brackets vanish, but its
jumps remain in the first-order Taylor correction.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.ito_exponential_mul_finiteVariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Y P) :
    let A := fun t ω ↦ Real.exp (X t ω)
    let E := fun t ω ↦ A t ω * Y t ω
    let haA : Adapted F A := fun t ↦ Real.continuous_exp.measurable.comp (hX.adapted t)
    let hrA := hX.hasCadlagPaths.continuous_comp Real.continuous_exp
    let haE : Adapted F E := fun t ↦ (haA t).mul (hY.adapted t)
    let hrE := hrA.mul hY.hasCadlagPaths
    let haL := haE.leftLimitProcess_of_usual hF hrE
    let hrL := hrE.hasCagladPaths_leftLimitProcess
    Indistinguishable (fun t ω ↦ E t ω - E 0 ω)
      (fun t ω ↦ hX.stochasticIntegral hF haL hrL t ω +
        hY.stochasticIntegral hF (haA.leftLimitProcess_of_usual hF hrA)
          hrA.hasCagladPaths_leftLimitProcess t ω +
        (1 / 2 : ℝ) * (hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
          hF haL hrL t ω +
        ∑' s : Ioc 0 t, (E s ω - Real.exp (leftLimitProcess X s ω) *
          leftLimitProcess Y s ω - Real.exp (leftLimitProcess X s ω) *
          leftLimitProcess Y s ω * jumpProcess X s ω -
          Real.exp (leftLimitProcess X s ω) * jumpProcess Y s ω)) P := by
  dsimp only
  let A := fun t ω ↦ Real.exp (X t ω)
  let E := fun t ω ↦ A t ω * Y t ω
  let haA : Adapted F A := fun t ↦ Real.continuous_exp.measurable.comp (hX.adapted t)
  let hrA := hX.hasCadlagPaths.continuous_comp Real.continuous_exp
  let haE : Adapted F E := fun t ↦ (haA t).mul (hY.adapted t)
  let hrE := hrA.mul hY.hasCadlagPaths
  let haL := haE.leftLimitProcess_of_usual hF hrE
  let hrL := hrE.hasCagladPaths_leftLimitProcess
  let haLA := haA.leftLimitProcess_of_usual hF hrA
  let hrLA := hrA.hasCagladPaths_leftLimitProcess
  let Z : Fin 2 → ℝ≥0 → Ω → ℝ := ![X, Y]
  have hZ : ∀ i, IsSemimartingale (Z i) F P := by
    intro i
    fin_cases i
    · exact hX
    · exact hY
  have hi := ito_finiteCoordinates_continuous_bracket hZ hF
    contDiff_exponentialProductCoordinates
  dsimp only at hi
  simp only [Fin.sum_univ_two, coordinateDeriv_exponentialProductCoordinates,
    coordinateSecondDeriv_exponentialProductCoordinates, exponentialProductCoordinates,
    Z, Matrix.cons_val_zero, Matrix.cons_val_one] at hi
  have hqY := hY.isQuadraticPureJump_of_finiteVariation hF hv
  have h01 := IsSemimartingale.stochasticIntegral_eq_zero_of_integrator_eq_zero
    (hX.isSemimartingale_continuousQuadraticCovariation hY hF) hF haLA hrLA
      (hX.continuousQuadraticCovariation_zero_of_quadraticPureJump_right hY hF hqY)
  have h10 := IsSemimartingale.stochasticIntegral_eq_zero_of_integrator_eq_zero
    (hY.isSemimartingale_continuousQuadraticCovariation hX hF) hF haLA hrLA
      (hY.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hX hF hqY)
  let ha0 : Adapted F (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) := fun _ ↦ measurable_const
  have hr0 : HasCadlagPaths (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) P :=
    Filter.Eventually.of_forall (fun _ ↦ IsContinuousPath.isCadlagPath continuous_const)
  have h11 := IsSemimartingale.stochasticIntegral_eq_zero_of_integrator_eq_zero
    (hY.isSemimartingale_continuousQuadraticCovariation hY hF) hF
    (ha0.leftLimitProcess_of_usual hF hr0) hr0.hasCagladPaths_leftLimitProcess
    (hY.continuousQuadraticCovariation_zero_of_quadraticPureJump_right hY hF hqY)
  have h00 := IsSemimartingale.stochasticIntegral_congr_integrator
    (hX.isSemimartingale_continuousQuadraticCovariation hX hF)
    (hX.isSemimartingale_continuousQuadraticVariation hF)
      hF haL hrL (hX.continuousQuadraticCovariation_self hF)
  filter_upwards [hi, h01, h10, h11, h00] with ω hiω h01ω h10ω h11ω h00ω t
  have h := hiω t
  rw [h01ω t, h10ω t, h11ω t, h00ω t] at h
  simp only [Pi.zero_apply, add_zero] at h
  rw [h]
  congr 1
  apply tsum_congr
  intro s
  ring

end ProbabilityTheory
