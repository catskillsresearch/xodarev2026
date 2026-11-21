/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrationByParts
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Associativity

/-! # Integrating the existing product formula

This identity uses the unique raw mixed bracket, integrator linearity and
associativity. The source initial terms are retained for arbitrary caglad H.
It does not yet identify the bracket of a stochastic integral.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_quadraticCovariation_eq
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr)
      ((hX.mul hY hF).stochasticIntegral hF ha hr -
        hY.stochasticIntegral hF
          (fun t ↦ (ha t).mul
            (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths t))
          (hr.mul hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess) -
        hX.stochasticIntegral hF
          (fun t ↦ (ha t).mul
            (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths t))
          (hr.mul hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess)) P := by
  let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let hJY := hY.isSemimartingale_stochasticIntegral hF haX hrX
  let hJX := hX.isSemimartingale_stochasticIntegral hF haY hrY
  let hProd := hX.mul hY hF
  have hrep := IsSemimartingale.stochasticIntegral_congr_integrator
    (hX.isSemimartingale_quadraticCovariation hY hF) ((hProd.sub hJY).sub hJX) hF ha hr
      (hX.quadraticCovariation_eq_product_sub_integrals hY hF)
  have hsub := (hProd.sub hJY).stochasticIntegral_sub_integrator hJX hF ha hr
  have hsub' := hProd.stochasticIntegral_sub_integrator hJY hF ha hr
  have hassocY := hY.stochasticIntegral_stochasticIntegral hF ha hr haX hrX
  have hassocX := hX.stochasticIntegral_stochasticIntegral hF ha hr haY hrY
  filter_upwards [hrep, hsub, hsub', hassocY, hassocX] with ω he hs hs' hy hx t
  rw [he t, hs t]
  simp only [Pi.sub_apply, hs' t, hy t, hx t]

end ProbabilityTheory
