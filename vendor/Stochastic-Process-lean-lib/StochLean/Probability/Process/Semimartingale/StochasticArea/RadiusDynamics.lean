/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.Radius
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousFVProduct

/-! # A C1 clock weight times the squared radius

This is the actual integral identity for two continuous zero-starting
semimartingales with a common raw bracket. The weight is any C1 function of
the continuous FV clock, not an assumed solution of a stochastic equation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.contDiff_clock_mul_sq_add_sq_eq_integrals
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0)
    (hf : ContDiff ℝ 1 f) :
    let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
      fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hf.continuous
    let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
      fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
    let hrR := (hcX.hasCagladPaths.continuous_comp (continuous_id.pow 2)).add
      (hcY.hasCagladPaths.continuous_comp (continuous_id.pow 2))
    let haD : Adapted F (fun t ω ↦ deriv f (Q t ω)) :=
      fun t ↦ hf.continuous_deriv_one.measurable.comp (hQ.adapted t)
    let hrD := hcQ.hasCagladPaths.continuous_comp hf.continuous_deriv_one
    Indistinguishable (fun t ω ↦ f (Q t ω) * (X t ω ^ 2 + Y t ω ^ 2))
      (fun t ω ↦ 2 * (hX.stochasticIntegral hF
          (fun r ↦ (haA r).mul (hX.adapted r)) (hrA.mul hcX.hasCagladPaths) t ω +
        hY.stochasticIntegral hF
          (fun r ↦ (haA r).mul (hY.adapted r)) (hrA.mul hcY.hasCagladPaths) t ω +
        hQ.stochasticIntegral hF haA hrA t ω) +
        hQ.stochasticIntegral hF
          (fun r ↦ (haR r).mul (haD r)) (hrR.mul hrD) t ω) P := by
  let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
    fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hf.continuous
  let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
  let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
  have hcR : HasContinuousPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
    filter_upwards [hcX, hcY] with ω hx hy
    exact (hx.pow 2).add (hy.pow 2)
  let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have heX : Indistinguishable
      (fun t ω ↦ f (Q t ω) * leftLimitProcess X t ω)
      (fun t ω ↦ f (Q t ω) * X t ω) P := by
    filter_upwards [hcX, h0X] with ω hx hz t
    by_cases ht : t = 0
    · subst t
      simp [hz]
    · rw [hx.leftLimitProcess_eq ht]
  have heY : Indistinguishable
      (fun t ω ↦ f (Q t ω) * leftLimitProcess Y t ω)
      (fun t ω ↦ f (Q t ω) * Y t ω) P := by
    filter_upwards [hcY, h0Y] with ω hy hz t
    by_cases ht : t = 0
    · subst t
      simp [hz]
    · rw [hy.leftLimitProcess_eq ht]
  filter_upwards [hQ.contDiff_clock_mul_eq_integrals hR hF hvQ hcQ hcR h0Q hf,
    hX.stochasticIntegral_sq_add_sq_of_common_raw_bracket hY hQ hF hqX hqY haA hrA,
    hX.stochasticIntegral_congr_integrand hF
      (fun r ↦ (haA r).mul (haX r)) (hrA.mul hrX)
      (fun r ↦ (haA r).mul (hX.adapted r)) (hrA.mul hcX.hasCagladPaths) heX,
    hY.stochasticIntegral_congr_integrand hF
      (fun r ↦ (haA r).mul (haY r)) (hrA.mul hrY)
      (fun r ↦ (haA r).mul (hY.adapted r)) (hrA.mul hcY.hasCagladPaths) heY]
      with ω hp hr hx hy t
  have hp' := hp t
  dsimp only [Pi.add_apply] at hp'
  rw [hr t, hx t, hy t] at hp'
  exact hp'

end ProbabilityTheory
