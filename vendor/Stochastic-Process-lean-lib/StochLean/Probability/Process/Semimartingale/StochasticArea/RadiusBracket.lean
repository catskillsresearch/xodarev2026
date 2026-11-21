/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.Radius
public import StochLean.Probability.Process.Semimartingale.StochasticArea.OrthogonalClock
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.FiniteVariationPerturbation

/-! # The continuous bracket of the squared radius

The actual common raw-bracket identity represents the squared radius as twice
an integral sum plus an FV clock. Continuous bracket algebra then identifies
its energy. No Brownian-law or moment premise replaces that calculation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}

private theorem radius_eq_twice_integralSum_add_clock
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) :
    Indistinguishable (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2)
      (fun t ω ↦ 2 * (hX.stochasticIntegral hF hX.adapted hcX.hasCagladPaths t ω +
        hY.stochasticIntegral hF hY.adapted hcY.hasCagladPaths t ω + Q t ω)) P := by
  filter_upwards [hX.sq_add_sq_eq_integrals_of_common_raw_bracket hY hF hqX hqY,
    hX.stochasticIntegral_leftLimit_of_continuous hF hX.adapted hcX,
    hY.stochasticIntegral_leftLimit_of_continuous hF hY.adapted hcY, h0X, h0Y]
      with ω hr hx hy hzX hzY t
  simpa only [hx t, hy t, hzX, hzY, Pi.zero_apply, zero_mul, sub_zero] using hr t

theorem IsSemimartingale.continuousQuadraticVariation_sq_add_sq_of_orthogonal_clock
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) :
    let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
    let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
    let haR : Adapted F (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) :=
      fun t ↦ ((hX.adapted t).pow_const 2).add ((hY.adapted t).pow_const 2)
    let hrR : HasCagladPaths (fun t ω ↦ X t ω ^ 2 + Y t ω ^ 2) P := by
      simpa only [pow_two, Pi.mul_def, Pi.add_def] using
        (hcX.hasCagladPaths.mul hcX.hasCagladPaths).add
          (hcY.hasCagladPaths.mul hcY.hasCagladPaths)
    Indistinguishable (hR.continuousQuadraticVariation hF)
      (fun t ω ↦ 4 * hQ.stochasticIntegral hF haR hrR t ω) P := by
  let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
  let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
  let hS := (hX.isSemimartingale_stochasticIntegral hF hX.adapted hcX.hasCagladPaths).add
    (hY.isSemimartingale_stochasticIntegral hF hY.adapted hcY.hasCagladPaths)
  have hcqX : Indistinguishable (hX.continuousQuadraticVariation hF) Q P := by
    filter_upwards [hX.continuousQuadraticVariation_eq_of_continuous hF hcX, hqX, h0X]
      with ω hc hq hz t
    simpa only [hq t, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hc t
  have hcqY : Indistinguishable (hY.continuousQuadraticVariation hF) Q P := by
    filter_upwards [hY.continuousQuadraticVariation_eq_of_continuous hF hcY, hqY, h0Y]
      with ω hc hq hz t
    simpa only [hq t, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hc t
  have he := hR.continuousQuadraticVariation_congr ((hS.add hQ).const_mul 2) hF
    (radius_eq_twice_integralSum_add_clock hX hY hF hqX hqY hcX hcY h0X h0Y)
  filter_upwards [he, (hS.add hQ).continuousQuadraticVariation_const_mul hF 2,
    hS.continuousQuadraticVariation_add_finiteVariation hQ hF hvQ,
    hX.continuousQuadraticVariation_stochasticIntegral_pair hY hQ hF hcqX hcqY ho
      hX.adapted hcX.hasCagladPaths hY.adapted hcY.hasCagladPaths]
      with ω heω hs hd hi t
  rw [heω t, hs t]
  simp only [Pi.smul_apply, smul_eq_mul, hd t, hi t]
  norm_num

theorem IsSemimartingale.continuousQuadraticCovariation_sq_add_sq_stochasticArea
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.quadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.quadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hvQ : HasFiniteVariationPaths Q P) (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) :
    let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
    let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
    Indistinguishable (hR.continuousQuadraticCovariation
      (hX.isSemimartingale_stochasticArea hY hF) hF) 0 P := by
  let hsq : ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) := by fun_prop
  let hR := (hX.contDiff_comp hF hsq).add (hY.contDiff_comp hF hsq)
  let hA := hX.isSemimartingale_stochasticArea hY hF
  let hS := (hX.isSemimartingale_stochasticIntegral hF hX.adapted hcX.hasCagladPaths).add
    (hY.isSemimartingale_stochasticIntegral hF hY.adapted hcY.hasCagladPaths)
  let haN : Adapted F (fun t ω ↦ (-1 : ℝ) * Y t ω) :=
    fun t ↦ (hY.adapted t).const_mul (-1)
  let hrN := hcY.hasCagladPaths.continuous_comp
    (continuous_const.mul continuous_id : Continuous (fun x : ℝ ↦ (-1 : ℝ) * x))
  let hN := (hX.isSemimartingale_stochasticIntegral hF haN hrN).add
    (hY.isSemimartingale_stochasticIntegral hF hX.adapted hcX.hasCagladPaths)
  have heA : Indistinguishable (hX.stochasticArea hY hF)
      (hX.stochasticIntegral hF haN hrN +
        hY.stochasticIntegral hF hX.adapted hcX.hasCagladPaths) P := by
    filter_upwards [hX.stochasticArea_eq_integrals_of_continuous hY hF hcX hcY,
      hX.stochasticIntegral_smul hF hY.adapted hcY.hasCagladPaths (-1)] with ω ha hn t
    simp only [ha t, Pi.sub_apply, Pi.add_apply, hn t, Pi.smul_apply, smul_eq_mul]
    ring
  have hcqX : Indistinguishable (hX.continuousQuadraticVariation hF) Q P := by
    filter_upwards [hX.continuousQuadraticVariation_eq_of_continuous hF hcX, hqX, h0X]
      with ω hc hq hz t
    simpa only [hq t, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hc t
  have hcqY : Indistinguishable (hY.continuousQuadraticVariation hF) Q P := by
    filter_upwards [hY.continuousQuadraticVariation_eq_of_continuous hF hcY, hqY, h0Y]
      with ω hc hq hz t
    simpa only [hq t, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using hc t
  have he := hR.continuousQuadraticCovariation_congr hA ((hS.add hQ).const_mul 2) hN hF
    (radius_eq_twice_integralSum_add_clock hX hY hF hqX hqY hcX hcY h0X h0Y) heA
  have hi := hX.continuousQuadraticCovariation_stochasticIntegral_pair hY hQ hF hcqX hcqY ho
    hX.adapted hcX.hasCagladPaths hY.adapted hcY.hasCagladPaths
    haN hrN hX.adapted hcX.hasCagladPaths
  have hz := hQ.stochasticIntegral_congr_integrand hF
    (fun t ↦ ((hX.adapted t).mul (haN t)).add ((hY.adapted t).mul (hX.adapted t)))
    ((hcX.hasCagladPaths.mul hrN).add (hcY.hasCagladPaths.mul hcX.hasCagladPaths))
    (IsSimplePredictable.zero F).adapted ((IsSimplePredictable.zero F).hasCagladPaths P)
    (Eventually.of_forall fun ω t ↦ by
      change X t ω * ((-1 : ℝ) * Y t ω) + Y t ω * X t ω = 0
      ring)
  filter_upwards [he, (hS.add hQ).continuousQuadraticCovariation_const_mul_left hN hF 2,
    hS.continuousQuadraticCovariation_add_finiteVariation_left hN hQ hF hvQ,
    hi.trans (hz.trans (hQ.stochasticIntegral_zero_integrand hF))]
      with ω heω hs hd hzω t
  rw [heω t, hs t]
  simp only [Pi.smul_apply, smul_eq_mul, hd t, hzω t, Pi.zero_apply, mul_zero]

end ProbabilityTheory
