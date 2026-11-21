/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.Basic
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousIntegral
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Subtraction

/-! # Covariation and continuous energy of the actual stochastic area

All brackets are the existing canonical raw or continuous owners. The area
identities follow from bilinearity and the proved brackets of actual integrals.
No independence, Brownian law, continuity or moment assumption is needed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_stochasticArea_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
    let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
    let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    Indistinguishable
      ((hX.isSemimartingale_stochasticArea hY hF).quadraticCovariation hZ hF)
      ((hY.isSemimartingale_quadraticCovariation hZ hF).stochasticIntegral hF haX hrX -
        (hX.isSemimartingale_quadraticCovariation hZ hF).stochasticIntegral hF haY hrY) P := by
  let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  filter_upwards [(hY.isSemimartingale_stochasticIntegral hF haX hrX).quadraticCovariation_sub_left
    (hX.isSemimartingale_stochasticIntegral hF haY hrY) hZ hF,
    hY.quadraticCovariation_stochasticIntegral_left hZ hF haX hrX,
    hX.quadraticCovariation_stochasticIntegral_left hZ hF haY hrY] with ω hs hxy hyx t
  exact (hs t).trans (congrArg₂ (fun a b : ℝ ↦ a - b) (hxy t) (hyx t))

theorem IsSemimartingale.continuousQuadraticCovariation_stochasticArea_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
    let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
    let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    Indistinguishable
      ((hX.isSemimartingale_stochasticArea hY hF).continuousQuadraticCovariation hZ hF)
      ((hY.isSemimartingale_continuousQuadraticCovariation hZ hF).stochasticIntegral
          hF haX hrX -
        (hX.isSemimartingale_continuousQuadraticCovariation hZ hF).stochasticIntegral
          hF haY hrY) P := by
  let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let hJY := hY.isSemimartingale_stochasticIntegral hF haX hrX
  filter_upwards [hJY.continuousQuadraticCovariation_sub_left
      (hX.isSemimartingale_stochasticIntegral hF haY hrY) hZ hF,
    hY.continuousQuadraticCovariation_stochasticIntegral_left hZ hF haX hrX,
    hX.continuousQuadraticCovariation_stochasticIntegral_left hZ hF haY hrY]
      with ω hs hxy hyx t
  exact (hs t).trans (congrArg₂ (fun a b : ℝ ↦ a - b) (hxy t) (hyx t))

theorem IsSemimartingale.continuousQuadraticCovariation_stochasticArea_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
    let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
    let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    Indistinguishable
      (hZ.continuousQuadraticCovariation (hX.isSemimartingale_stochasticArea hY hF) hF)
      ((hY.isSemimartingale_continuousQuadraticCovariation hZ hF).stochasticIntegral
          hF haX hrX -
        (hX.isSemimartingale_continuousQuadraticCovariation hZ hF).stochasticIntegral
          hF haY hrY) P :=
  (hZ.continuousQuadraticCovariation_comm (hX.isSemimartingale_stochasticArea hY hF) hF).trans
    (hX.continuousQuadraticCovariation_stochasticArea_left hY hZ hF)

theorem IsSemimartingale.continuousQuadraticVariation_stochasticArea
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
    let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
    let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    Indistinguishable
      ((hX.isSemimartingale_stochasticArea hY hF).continuousQuadraticVariation hF)
      (fun t ω ↦
        (hY.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral hF
          (fun r ↦ (haX r).mul (haX r)) (hrX.mul hrX) t ω +
        (hX.isSemimartingale_continuousQuadraticCovariation hX hF).stochasticIntegral hF
          (fun r ↦ (haY r).mul (haY r)) (hrY.mul hrY) t ω -
        2 * (hY.isSemimartingale_continuousQuadraticCovariation hX hF).stochasticIntegral hF
          (fun r ↦ (haX r).mul (haY r)) (hrX.mul hrY) t ω) P := by
  let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let hJY := hY.isSemimartingale_stochasticIntegral hF haX hrX
  let hJX := hX.isSemimartingale_stochasticIntegral hF haY hrY
  let hA := hX.isSemimartingale_stochasticArea hY hF
  filter_upwards [hA.continuousQuadraticCovariation_self hF,
    hJY.continuousQuadraticCovariation_sub_left hJX hA hF,
    hJY.continuousQuadraticCovariation_sub_right hJY hJX hF,
    hJX.continuousQuadraticCovariation_sub_right hJY hJX hF,
    hJX.continuousQuadraticCovariation_comm hJY hF,
    hY.continuousQuadraticCovariation_stochasticIntegral_both hY hF haX hrX haX hrX,
    hX.continuousQuadraticCovariation_stochasticIntegral_both hX hF haY hrY haY hrY,
    hY.continuousQuadraticCovariation_stochasticIntegral_both hX hF haX hrX haY hrY]
      with ω hself hs hr₁ hr₂ hc hyy hxx hyx t
  have he := hs t
  change hA.continuousQuadraticCovariation hA hF t ω =
    hJY.continuousQuadraticCovariation (hJY.sub hJX) hF t ω -
      hJX.continuousQuadraticCovariation (hJY.sub hJX) hF t ω at he
  rw [hself t, hr₁ t, hr₂ t] at he
  simp only [Pi.sub_apply] at he
  rw [hc t, hyy t, hxx t, hyx t] at he
  exact he.trans (by ring)

end ProbabilityTheory
