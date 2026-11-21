/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.CadlagFVChangeOfVariables
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Algebra

/-! # Ordinary derivative integrands along continuous zero-starting FV clocks

The source initial term and the positive-time jump correction vanish by
proved hypotheses. Continuity alone would not identify the source left limit
at zero; the explicit zero-start condition is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticIntegral_derivative_of_continuous_finiteVariation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Q : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Q P) (hc : HasContinuousPaths Q P)
    (h0 : Q 0 =ᵐ[P] 0) (hf : ContDiff ℝ 1 f) :
    let ha : Adapted F (fun t ω ↦ deriv f (Q t ω)) :=
      fun t ↦ hf.continuous_deriv_one.measurable.comp (hQ.adapted t)
    let hr := hc.hasCagladPaths.continuous_comp hf.continuous_deriv_one
    Indistinguishable (hQ.stochasticIntegral hF ha hr)
      (fun t ω ↦ f (Q t ω) - f 0) P := by
  let ha : Adapted F (fun t ω ↦ deriv f (Q t ω)) :=
    fun t ↦ hf.continuous_deriv_one.measurable.comp (hQ.adapted t)
  let hr := hc.hasCagladPaths.continuous_comp hf.continuous_deriv_one
  let haL : Adapted F (fun t ω ↦ deriv f (leftLimitProcess Q t ω)) :=
    fun t ↦ hf.continuous_deriv_one.measurable.comp
      (hQ.adapted.leftLimitProcess_of_usual hF hQ.hasCadlagPaths t)
  let hrL := hQ.hasCadlagPaths.hasCagladPaths_leftLimitProcess.continuous_comp
    hf.continuous_deriv_one
  have he : Indistinguishable (fun t ω ↦ deriv f (leftLimitProcess Q t ω))
      (fun t ω ↦ deriv f (Q t ω)) P := by
    filter_upwards [hc, h0] with ω hcω h0ω t
    by_cases ht : t = 0
    · subst t
      simp only [leftLimitProcess_zero, h0ω, Pi.zero_apply]
    · rw [hcω.leftLimitProcess_eq ht]
  filter_upwards [hQ.contDiff_change_of_variables_of_finiteVariation hF hv hf,
    hQ.stochasticIntegral_congr_integrand hF haL hrL ha hr he, hc, h0]
      with ω hi heω hcω h0ω t
  have hz : (∑' s : Ioc 0 t, (f (Q s ω) - f (leftLimitProcess Q s ω) -
      deriv f (leftLimitProcess Q s ω) * jumpProcess Q s ω)) = 0 := by
    trans ∑' _s : Ioc 0 t, (0 : ℝ)
    · apply tsum_congr
      intro s
      rw [hcω.leftLimitProcess_eq (ne_of_gt s.2.1),
        hcω.jumpProcess_eq_zero (ne_of_gt s.2.1)]
      ring
    · exact tsum_zero
  have h := hi t
  rw [heω t, hz, h0ω] at h
  simpa only [Pi.zero_apply, mul_zero, sub_zero, add_zero] using h.symm

end ProbabilityTheory
