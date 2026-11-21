/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.ExponentialEquation
public import StochLean.Probability.Process.Semimartingale.Complex.ContinuousLocalMartingale

/-! # The actual compensated area exponential is a complex local martingale

The proved Ito cancellation expresses its increment using actual integrals
against the continuous local-martingale coordinates. The initial process is
handled by the existing masked constant-local-martingale theorem, without an
unjustified initial-integrability assumption.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsContinuousLocalMartingale.isComplexLocalMartingale_stochasticAreaExponential
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F]
    {X Y Q : ℝ≥0 → Ω → ℝ}
    (hX : IsContinuousLocalMartingale X F P) (hY : IsContinuousLocalMartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF) Q P)
    (hqY : Indistinguishable ((hY.isSemimartingale hF).quadraticVariation hF) Q P)
    (ho : Indistinguishable
      ((hX.isSemimartingale hF).continuousQuadraticCovariation (hY.isSemimartingale hF) hF) 0 P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    IsComplexLocalMartingale
      ((hX.isSemimartingale hF).stochasticAreaExponential (hY.isSemimartingale hF) hF Q u T)
      F P := by
  let hSX := hX.isSemimartingale hF
  let hSY := hY.isSemimartingale hF
  let hE := hSX.isComplexSemimartingale_stochasticAreaExponential hSY hQ hF u T
  let haL := Adapted.complexLeftLimitProcess_of_usual hE.adapted hF hE.hasCadlagPaths
  let hrL := hE.hasCadlagPaths.hasCagladPaths_complexLeftLimitProcess
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
  let haAX : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * X t ω) :=
    fun t ↦ (haA t).mul (hSX.adapted t)
  let hrAX := hrA.mul hX.2.hasCagladPaths
  let haAY : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) * Y t ω) :=
    fun t ↦ (haA t).mul (hSY.adapted t)
  let hrAY := hrA.mul hY.2.hasCagladPaths
  have hJAX := hX.isComplexLocalMartingale_complexIntegrandIntegral hF
    (fun t ↦ (haL t).mul (Complex.continuous_ofReal.measurable.comp (haAX t)))
    (hrL.mul (hrAX.continuous_comp Complex.continuous_ofReal))
  have hJAY := hY.isComplexLocalMartingale_complexIntegrandIntegral hF
    (fun t ↦ (haL t).mul (Complex.continuous_ofReal.measurable.comp (haAY t)))
    (hrL.mul (hrAY.continuous_comp Complex.continuous_ofReal))
  have hJYX := hY.isComplexLocalMartingale_complexIntegrandIntegral hF
    (fun t ↦ (haL t).mul (Complex.continuous_ofReal.measurable.comp (hSX.adapted t)))
    (hrL.mul (hX.2.hasCagladPaths.continuous_comp Complex.continuous_ofReal))
  have hJXY := hX.isComplexLocalMartingale_complexIntegrandIntegral hF
    (fun t ↦ (haL t).mul (Complex.continuous_ofReal.measurable.comp (hSY.adapted t)))
    (hrL.mul (hY.2.hasCagladPaths.continuous_comp Complex.continuous_ofReal))
  have hN := (hJAX.const_mul hF (-1)).add (hJAY.const_mul hF (-1)) hF
  have hA := (hJYX.add (hJXY.const_mul hF (-1)) hF).const_mul hF (Complex.I * (u : ℂ))
  have hSum := hN.add hA hF
  have hC := isComplexLocalMartingale_const_initial (P := P) (hE.adapted 0)
  apply (hC.add hSum hF).congr hF hE.adapted
  filter_upwards [hSX.stochasticAreaExponential_sub_initial_eq_integrals hSY hQ hF hqX hqY ho
    hX.2 hY.2 hvQ hcQ h0X h0Y h0Q u T] with ω he t
  have he' := he t
  dsimp only [Pi.add_apply]
  linear_combination -he'

end ProbabilityTheory
