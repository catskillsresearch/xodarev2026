/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.Basic
public import StochLean.Probability.Process.Semimartingale.Ito.Preservation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Associativity
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation

/-! # The actual squared-radius differential under a common raw clock

The sum of the two defining square-bracket identities gives the squared
radius. Integrator linearity and associativity then identify every caglad
integral against it. The common raw clock may start at a nonzero value; no
independence, Brownian law or initial integrability is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.sq_add_sq_eq_integrals_of_common_raw_bracket
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P) :
    let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
    let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
    let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    Indistinguishable (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2)
      (fun t ω ↦ 2 * (hX.stochasticIntegral hF haX hrX t ω +
        hY.stochasticIntegral hF haY hrY t ω + Q t ω)) P := by
  filter_upwards [hqX, hqY] with ω hx hy t
  have hx' := hx t
  have hy' := hy t
  dsimp only [quadraticVariation] at hx' hy'
  linarith

theorem IsSemimartingale.stochasticIntegral_sq_add_sq_of_common_raw_bracket
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
    let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
    let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
    let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
    let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    Indistinguishable (hR.stochasticIntegral hF ha hr)
      (fun t ω ↦ 2 * (hX.stochasticIntegral hF
        (fun r ↦ (ha r).mul (haX r)) (hr.mul hrX) t ω +
        hY.stochasticIntegral hF (fun r ↦ (ha r).mul (haY r)) (hr.mul hrY) t ω +
        hQ.stochasticIntegral hF ha hr t ω)) P := by
  let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
  let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
  let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let hJX := hX.isSemimartingale_stochasticIntegral hF haX hrX
  let hJY := hY.isSemimartingale_stochasticIntegral hF haY hrY
  let hS := (hJX.add hJY).add hQ
  have he := hR.stochasticIntegral_congr_integrator (hS.const_mul 2) hF ha hr
    (hX.sq_add_sq_eq_integrals_of_common_raw_bracket hY hF hqX hqY)
  filter_upwards [he, hS.stochasticIntegral_const_mul_integrator hF ha hr 2,
    (hJX.add hJY).stochasticIntegral_add_integrator hQ hF ha hr,
    hJX.stochasticIntegral_add_integrator hJY hF ha hr,
    hX.stochasticIntegral_stochasticIntegral hF ha hr haX hrX,
    hY.stochasticIntegral_stochasticIntegral hF ha hr haY hrY]
      with ω heω htwo hsum hsum' hx hy t
  rw [heω t, htwo t]
  simp only [Pi.smul_apply, smul_eq_mul, hsum t, Pi.add_apply, hsum' t, hx t, hy t]

end ProbabilityTheory
