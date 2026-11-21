/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousFVProduct
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationPreservation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousIntegral
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.FiniteVariationPerturbation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift

/-! # Continuous brackets under C1 continuous-FV clock multipliers

The actual product formula splits the product into an integral and an FV
remainder. Removing that remainder uses the continuous bracket only; no false
zero-initial convention is imposed on the raw bracket or on the multiplier.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Q X Y : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_contDiff_clock_mul_left
    (hQ : IsSemimartingale Q F P) (hX : IsSemimartingale X F P)
    (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (hcX : HasContinuousPaths X P) (h0 : Q 0 =ᵐ[P] 0) (hf : ContDiff ℝ 1 f) :
    let hA := isSemimartingale_contDiff_of_continuous_finiteVariation
      hQ.adapted hF hv hcQ hf
    let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
      fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hf.continuous
    Indistinguishable ((hA.mul hX hF).continuousQuadraticCovariation hY hF)
      ((hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral
        hF haA hrA) P := by
  let hA := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hv hcQ hf
  let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
    fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hf.continuous
  let haD : Adapted F (fun t ω ↦ X t ω * deriv f (Q t ω)) :=
    fun t ↦ (hX.adapted t).mul (hf.continuous_deriv_one.measurable.comp (hQ.adapted t))
  let hrD := hcX.hasCagladPaths.mul
    (hcQ.hasCagladPaths.continuous_comp hf.continuous_deriv_one)
  let hJ := hX.isSemimartingale_stochasticIntegral hF haA hrA
  let hD := hQ.isSemimartingale_stochasticIntegral hF haD hrD
  have hvD := hQ.hasFiniteVariationPaths_stochasticIntegral hF hv haD hrD
  have he := (hA.mul hX hF).continuousQuadraticCovariation_congr hY (hJ.add hD) hY hF
    (hQ.contDiff_clock_mul_eq_integrals hX hF hv hcQ hcX h0 hf)
    (Eventually.of_forall fun _ _ ↦ rfl)
  exact he.trans ((hJ.continuousQuadraticCovariation_add_finiteVariation_left hY hD hF hvD).trans
    (hX.continuousQuadraticCovariation_stochasticIntegral_left hY hF haA hrA))

theorem IsSemimartingale.continuousQuadraticVariation_contDiff_clock_mul
    (hQ : IsSemimartingale Q F P) (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (hcX : HasContinuousPaths X P) (h0 : Q 0 =ᵐ[P] 0) (hf : ContDiff ℝ 1 f) :
    let hA := isSemimartingale_contDiff_of_continuous_finiteVariation
      hQ.adapted hF hv hcQ hf
    let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
      fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
    let hrA := hcQ.hasCagladPaths.continuous_comp hf.continuous
    Indistinguishable ((hA.mul hX hF).continuousQuadraticVariation hF)
      ((hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
        (H := fun t ω ↦ f (Q t ω) ^ 2) hF
        (fun t ↦ (haA t).pow_const 2)
        (by simpa only [pow_two, Pi.mul_def] using hrA.mul hrA)) P := by
  let hA := isSemimartingale_contDiff_of_continuous_finiteVariation
    hQ.adapted hF hv hcQ hf
  let haA : Adapted F (fun t ω ↦ f (Q t ω)) :=
    fun t ↦ hf.continuous.measurable.comp (hQ.adapted t)
  let hrA := hcQ.hasCagladPaths.continuous_comp hf.continuous
  let haD : Adapted F (fun t ω ↦ X t ω * deriv f (Q t ω)) :=
    fun t ↦ (hX.adapted t).mul (hf.continuous_deriv_one.measurable.comp (hQ.adapted t))
  let hrD := hcX.hasCagladPaths.mul
    (hcQ.hasCagladPaths.continuous_comp hf.continuous_deriv_one)
  let hJ := hX.isSemimartingale_stochasticIntegral hF haA hrA
  let hD := hQ.isSemimartingale_stochasticIntegral hF haD hrD
  have hvD := hQ.hasFiniteVariationPaths_stochasticIntegral hF hv haD hrD
  have he := (hA.mul hX hF).continuousQuadraticVariation_congr (hJ.add hD) hF
    (hQ.contDiff_clock_mul_eq_integrals hX hF hv hcQ hcX h0 hf)
  let hC := hX.isSemimartingale_continuousQuadraticCovariation hX hF
  let hB := hX.isSemimartingale_continuousQuadraticVariation hF
  have hi := hC.stochasticIntegral_congr_integrator hB
      hF (fun t ↦ (haA t).mul (haA t)) (hrA.mul hrA)
      (hX.continuousQuadraticCovariation_self hF)
  have hs := hB.stochasticIntegral_congr_integrand hF
      (fun t ↦ (haA t).mul (haA t)) (hrA.mul hrA)
      (fun t ↦ (haA t).pow_const 2) (by simpa only [pow_two, Pi.mul_def] using hrA.mul hrA)
      (Eventually.of_forall fun _ _ ↦ (pow_two _).symm)
  exact he.trans ((hJ.continuousQuadraticVariation_add_finiteVariation hD hF hvD).trans
    ((hJ.continuousQuadraticCovariation_self hF).symm.trans
      ((hX.continuousQuadraticCovariation_stochasticIntegral_both hX hF haA hrA haA hrA).trans
        (hi.trans hs))))

end ProbabilityTheory
