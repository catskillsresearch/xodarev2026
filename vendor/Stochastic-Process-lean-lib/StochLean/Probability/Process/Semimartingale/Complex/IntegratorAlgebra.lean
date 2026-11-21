/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance

/-! # Real-integrator algebra for complex integrands

All identities compare the existing real coordinate integral selectors by
indistinguishability. Initial products are retained by those scalar owners.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}

theorem IsSemimartingale.complexIntegrandIntegral_congr_integrator
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (he : Indistinguishable X Y P) :
    Indistinguishable (hX.complexIntegrandIntegral hF ha hr)
      (hY.complexIntegrandIntegral hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_congr_integrator hY hF
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re) he,
    hX.stochasticIntegral_congr_integrator hY hF
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im) he] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

theorem IsSemimartingale.complexIntegrandIntegral_add_integrator
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable ((hX.add hY).complexIntegrandIntegral hF ha hr)
      (hX.complexIntegrandIntegral hF ha hr + hY.complexIntegrandIntegral hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_add_integrator hY hF
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re),
    hX.stochasticIntegral_add_integrator hY hF
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im)] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

theorem IsSemimartingale.complexIntegrandIntegral_sub_integrator
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable ((hX.sub hY).complexIntegrandIntegral hF ha hr)
      (hX.complexIntegrandIntegral hF ha hr - hY.complexIntegrandIntegral hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_sub_integrator hY hF
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re),
    hX.stochasticIntegral_sub_integrator hY hF
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im)] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

theorem IsSemimartingale.complexIntegrandIntegral_const_mul_integrator
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (c : ℝ) :
    Indistinguishable ((hX.const_mul c).complexIntegrandIntegral hF ha hr)
      (c • hX.complexIntegrandIntegral hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_const_mul_integrator hF
    (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
    (hr.continuous_comp Complex.continuous_re) c,
    hX.stochasticIntegral_const_mul_integrator hF
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im) c] with ω hR hI t
  apply Complex.ext
  · simpa only [complexIntegrandIntegral, complexProcess, Pi.smul_apply,
      Complex.smul_re] using hR t
  · simpa only [complexIntegrandIntegral, complexProcess, Pi.smul_apply,
      Complex.smul_im] using hI t

end ProbabilityTheory
