/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.RadiusDynamics
public import StochLean.Probability.Process.Semimartingale.StochasticArea.RiccatiDynamics
public import StochLean.Probability.Process.Semimartingale.StochasticArea.Exponent

/-! # The actual real-coordinate dynamics of the area exponent

The weighted-radius product formula and the two Riccati derivatives give the
real-coordinate integral representation. No drift identity or local-martingale
property of the candidate exponential is supplied as a premise.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticAreaExponent_re_eq_integrals
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
    let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
      fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hα.continuous
    let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
      fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
    let hrR := (hcX.hasCagladPaths.continuous_comp (continuous_id.pow 2)).add
      (hcY.hasCagladPaths.continuous_comp (continuous_id.pow 2))
    let haD : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2) :=
      fun t ↦ ((haA t).pow_const 2).sub measurable_const
    let hrD := hcQ.hasCagladPaths.continuous_comp
      ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2)))
    Indistinguishable (fun t ω ↦ (hX.stochasticAreaExponent hY hF Q u T t ω).re)
      (fun t ω ↦ levyAreaBeta u T 0 -
        hX.stochasticIntegral hF
          (fun r ↦ (haA r).mul (hX.adapted r)) (hrA.mul hcX.hasCagladPaths) t ω -
        hY.stochasticIntegral hF
          (fun r ↦ (haA r).mul (hY.adapted r)) (hrA.mul hcY.hasCagladPaths) t ω -
        (1 / 2 : ℝ) * hQ.stochasticIntegral hF
          (fun r ↦ (haR r).mul (haD r)) (hrR.mul hrD) t ω) P := by
  let hα : ContDiff ℝ 1 (levyAreaAlpha u T) := contDiff_levyAreaAlpha u T
  let haA : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω)) :=
    fun t ↦ hα.continuous.measurable.comp (hQ.adapted t)
  let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
    fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
  let hrR := (hcX.hasCagladPaths.continuous_comp (continuous_id.pow 2)).add
    (hcY.hasCagladPaths.continuous_comp (continuous_id.pow 2))
  let haD : Adapted F (fun t ω ↦ levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2) :=
    fun t ↦ ((haA t).pow_const 2).sub measurable_const
  let hrD := hcQ.hasCagladPaths.continuous_comp
    ((hα.continuous.pow 2).sub (continuous_const : Continuous (fun _ : ℝ ↦ u ^ 2)))
  let haD' : Adapted F (fun t ω ↦ deriv (levyAreaAlpha u T) (Q t ω)) :=
    fun t ↦ hα.continuous_deriv_one.measurable.comp (hQ.adapted t)
  let hrD' := hcQ.hasCagladPaths.continuous_comp hα.continuous_deriv_one
  have he : Indistinguishable
      (fun t ω ↦ (X t ω ^ 2 + Y t ω ^ 2) * deriv (levyAreaAlpha u T) (Q t ω))
      (fun t ω ↦ (X t ω ^ 2 + Y t ω ^ 2) *
        (levyAreaAlpha u T (Q t ω) ^ 2 - u ^ 2)) P := by
    exact Eventually.of_forall fun ω t ↦ congrArg ((X t ω ^ 2 + Y t ω ^ 2) * ·)
      (hasDerivAt_levyAreaAlpha u T (Q t ω)).deriv
  filter_upwards [hX.contDiff_clock_mul_sq_add_sq_eq_integrals hY hQ hF hqX hqY
      hcX hcY hvQ hcQ h0X h0Y h0Q hα,
    hQ.stochasticIntegral_levyAreaBeta_drift hF hvQ hcQ h0Q u T,
    hQ.stochasticIntegral_congr_integrand hF
      (fun r ↦ (haR r).mul (haD' r)) (hrR.mul hrD')
      (fun r ↦ (haR r).mul (haD r)) (hrR.mul hrD) he]
      with ω hp hb hd t
  have hp' := hp t
  rw [hd t] at hp'
  have hb' := hb t
  dsimp only [stochasticAreaExponent, complexProcess]
  linarith

end ProbabilityTheory
