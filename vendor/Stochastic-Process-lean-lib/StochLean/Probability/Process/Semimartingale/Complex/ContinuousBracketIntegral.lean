/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.BracketIntegral
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegralDecomposition

/-! # Raw and continuous brackets agree under integration from zero plus

The integrand must vanish at the source time zero. Without this condition
the raw initial square or product cannot be discarded, even for constants.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ} {Z G : ℝ≥0 → Ω → ℂ}

theorem IsSemimartingale.stochasticIntegral_raw_continuous_square_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (h0 : H 0 =ᵐ[P] 0) :
    Indistinguishable
      ((hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF ha hr)
      ((hX.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_quadraticVariation_continuous_jump_decomposition
    hF ha hr, hc, h0] with ω hi hcω hz t
  have hj (s : Ioc 0 t) : jumpProcess X s ω = 0 :=
    hcω.jumpProcess_eq_zero (ne_of_gt s.2.1)
  simpa only [hz, Pi.zero_apply, zero_mul, zero_add, hj, zero_pow (by decide : 2 ≠ 0),
    mul_zero, tsum_zero, add_zero] using hi t

theorem IsSemimartingale.stochasticIntegral_raw_continuous_mixed_of_continuous_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (ha : Adapted F H) (hr : HasCagladPaths H P)
    (h0 : H 0 =ᵐ[P] 0) :
    Indistinguishable
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr)
      ((hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral
        hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_quadraticCovariation_continuous_jump_decomposition
    hY hF ha hr, hc, h0] with ω hi hcω hz t
  have hj (s : Ioc 0 t) : jumpProcess X s ω = 0 :=
    hcω.jumpProcess_eq_zero (ne_of_gt s.2.1)
  simpa only [hz, Pi.zero_apply, zero_mul, zero_add, hj, mul_zero, tsum_zero, add_zero]
    using hi t

theorem IsSemimartingale.complexIntegrandIntegral_raw_continuous_square_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (ha : Adapted F G) (hr : HasCagladPaths G P) (h0 : G 0 =ᵐ[P] 0) :
    Indistinguishable
      ((hX.isSemimartingale_quadraticVariation hF).complexIntegrandIntegral hF ha hr)
      ((hX.isSemimartingale_continuousQuadraticVariation hF).complexIntegrandIntegral
        hF ha hr) P := by
  have hR : (fun ω ↦ (G 0 ω).re) =ᵐ[P] 0 := h0.mono (fun _ h ↦ congrArg Complex.re h)
  have hI : (fun ω ↦ (G 0 ω).im) =ᵐ[P] 0 := h0.mono (fun _ h ↦ congrArg Complex.im h)
  filter_upwards [hX.stochasticIntegral_raw_continuous_square_of_continuous hF hc
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re) hR,
    hX.stochasticIntegral_raw_continuous_square_of_continuous hF hc
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im) hI] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

theorem IsSemimartingale.complexIntegrandIntegral_raw_continuous_mixed_of_continuous_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (ha : Adapted F G) (hr : HasCagladPaths G P)
    (h0 : G 0 =ᵐ[P] 0) :
    Indistinguishable
      ((hX.isSemimartingale_quadraticCovariation hY hF).complexIntegrandIntegral hF ha hr)
      ((hX.isSemimartingale_continuousQuadraticCovariation hY hF).complexIntegrandIntegral
        hF ha hr) P := by
  have hR : (fun ω ↦ (G 0 ω).re) =ᵐ[P] 0 := h0.mono (fun _ h ↦ congrArg Complex.re h)
  have hI : (fun ω ↦ (G 0 ω).im) =ᵐ[P] 0 := h0.mono (fun _ h ↦ congrArg Complex.im h)
  filter_upwards [hX.stochasticIntegral_raw_continuous_mixed_of_continuous_left hY hF hc
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re) hR,
    hX.stochasticIntegral_raw_continuous_mixed_of_continuous_left hY hF hc
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im) hI] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

theorem IsComplexSemimartingale.stochasticIntegral_raw_continuous_bracket_of_continuous
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (hc : HasContinuousPaths Z P)
    (ha : Adapted F G) (hr : HasCagladPaths G P) (h0 : G 0 =ᵐ[P] 0) :
    Indistinguishable
      ((hZ.isComplexSemimartingale_quadraticVariation hF).stochasticIntegral hF ha hr)
      ((hZ.isComplexSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
        hF ha hr) P := by
  have hcR : HasContinuousPaths (fun t ω ↦ (Z t ω).re) P :=
    hc.mono (fun _ h ↦ Complex.continuous_re.comp h)
  have hcI : HasContinuousPaths (fun t ω ↦ (Z t ω).im) P :=
    hc.mono (fun _ h ↦ Complex.continuous_im.comp h)
  filter_upwards [hZ.stochasticIntegral_quadraticVariation_coordinates hF ha hr,
    hZ.stochasticIntegral_continuousQuadraticVariation_coordinates hF ha hr,
    hZ.1.complexIntegrandIntegral_raw_continuous_square_of_continuous hF hcR ha hr h0,
    hZ.2.complexIntegrandIntegral_raw_continuous_square_of_continuous hF hcI ha hr h0,
    hZ.1.complexIntegrandIntegral_raw_continuous_mixed_of_continuous_left hZ.2 hF hcR ha hr h0]
      with ω hraw hcont hR hI hRI t
  rw [hraw t, hcont t, hR t, hI t, hRI t]

end ProbabilityTheory
