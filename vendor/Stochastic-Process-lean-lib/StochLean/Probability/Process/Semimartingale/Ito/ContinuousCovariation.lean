/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.FiniteVariationResidual
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousIntegral
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump

/-! # Continuous covariation chain rule for C2 transformations

The proved Ito residual has finite variation and hence zero continuous
covariation. The first-order integral supplies the entire continuous bracket.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_contDiff_comp_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hf : ContDiff ℝ 2 f) :
    let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
    let ha : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
      fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
    let hr := hX.hasCadlagPaths.continuous_comp hd.continuous
    Indistinguishable ((hX.contDiff_comp hF hf).continuousQuadraticCovariation hY hF)
      ((hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral hF
        (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess) P := by
  dsimp only
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
  let hr := hX.hasCadlagPaths.continuous_comp hd.continuous
  let hJ := hX.isSemimartingale_stochasticIntegral hF
    (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess
  let hG := hX.contDiff_comp hF hf
  let hV := hG.sub hJ
  have hv := hX.hasFiniteVariationPaths_contDiff_sub_derivativeIntegral hF hf
  have he : Indistinguishable
      (hX.stochasticIntegral hF (ha.leftLimitProcess_of_usual hF hr)
        hr.hasCagladPaths_leftLimitProcess +
        ((fun t ω ↦ f (X t ω)) - hX.stochasticIntegral hF
          (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess))
      (fun t ω ↦ f (X t ω)) P := ae_of_all _ (fun ω t ↦ by
        simp only [Pi.add_apply, Pi.sub_apply]
        ring)
  have hc := (hJ.add hV).continuousQuadraticCovariation_congr hY hG hY hF he
    (ae_of_all _ (fun _ _ ↦ rfl))
  have hz := hV.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hY hF
    (hV.isQuadraticPureJump_of_finiteVariation hF hv)
  filter_upwards [hc, hJ.continuousQuadraticCovariation_add_left hV hY hF, hz,
    hX.continuousQuadraticCovariation_stochasticIntegral_left hY hF
      (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess]
        with ω hcω hs hzω hi t
  exact (hcω t).symm.trans ((hs t).trans (by
    simp only [Pi.add_apply, hzω t, Pi.zero_apply, add_zero]
    exact hi t))

theorem IsSemimartingale.continuousQuadraticCovariation_contDiff_comp_self
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
    let ha : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
      fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
    let hr := hX.hasCadlagPaths.continuous_comp hd.continuous
    Indistinguishable ((hX.contDiff_comp hF hf).continuousQuadraticCovariation hX hF)
      ((hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF
        (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess) P := by
  dsimp only
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
  let hr := hX.hasCadlagPaths.continuous_comp hd.continuous
  exact (hX.continuousQuadraticCovariation_contDiff_comp_left hX hF hf).trans
    ((hX.isSemimartingale_continuousQuadraticCovariation hX hF).stochasticIntegral_congr_integrator
      (hX.isSemimartingale_continuousQuadraticVariation hF) hF
      (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess
      (hX.continuousQuadraticCovariation_self hF))

end ProbabilityTheory
