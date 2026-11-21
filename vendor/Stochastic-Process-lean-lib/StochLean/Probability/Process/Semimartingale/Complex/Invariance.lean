/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.Complex.ZeroIntegrator

/-! # Version invariance and real-coordinate reduction for complex integrals

All statements are indistinguishability identities for the existing coordinate
integrals. No equality of arbitrarily chosen versions or zero-initial convention
is imposed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z W H K : ℝ≥0 → Ω → ℂ}

theorem IsSemimartingale.complexIntegrandIntegral_congr_integrand
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) (he : Indistinguishable H K P) :
    Indistinguishable (hX.complexIntegrandIntegral hF haH hrH)
      (hX.complexIntegrandIntegral hF haK hrK) P := by
  filter_upwards [hX.stochasticIntegral_congr_integrand hF
      (fun t ↦ Complex.continuous_re.measurable.comp (haH t))
      (hrH.continuous_comp Complex.continuous_re)
      (fun t ↦ Complex.continuous_re.measurable.comp (haK t))
      (hrK.continuous_comp Complex.continuous_re)
      (he.mono fun _ h t ↦ congrArg Complex.re (h t)),
    hX.stochasticIntegral_congr_integrand hF
      (fun t ↦ Complex.continuous_im.measurable.comp (haH t))
      (hrH.continuous_comp Complex.continuous_im)
      (fun t ↦ Complex.continuous_im.measurable.comp (haK t))
      (hrK.continuous_comp Complex.continuous_im)
      (he.mono fun _ h t ↦ congrArg Complex.im (h t))] with ω hR hI t
  exact Complex.ext (hR t) (hI t)

theorem IsComplexSemimartingale.stochasticIntegral_congr_integrator
    (hZ : IsComplexSemimartingale Z F P) (hW : IsComplexSemimartingale W F P)
    (hF : F.IsUsual P) (ha : Adapted F H) (hr : HasCagladPaths H P)
    (he : Indistinguishable Z W P) :
    Indistinguishable (hZ.stochasticIntegral hF ha hr)
      (hW.stochasticIntegral hF ha hr) P := by
  filter_upwards [hZ.1.complexIntegrandIntegral_congr_integrator hW.1 hF ha hr
      (he.mono fun _ h t ↦ congrArg Complex.re (h t)),
    hZ.2.complexIntegrandIntegral_congr_integrator hW.2 hF ha hr
      (he.mono fun _ h t ↦ congrArg Complex.im (h t))] with ω hR hI t
  exact congrArg₂ (fun a b : ℂ ↦ a + Complex.I * b) (hR t) (hI t)

theorem IsComplexSemimartingale.stochasticIntegral_congr_integrand
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) (he : Indistinguishable H K P) :
    Indistinguishable (hZ.stochasticIntegral hF haH hrH)
      (hZ.stochasticIntegral hF haK hrK) P := by
  filter_upwards [hZ.1.complexIntegrandIntegral_congr_integrand hF haH hrH haK hrK he,
    hZ.2.complexIntegrandIntegral_congr_integrand hF haH hrH haK hrK he] with ω hR hI t
  exact congrArg₂ (fun a b : ℂ ↦ a + Complex.I * b) (hR t) (hI t)

theorem IsComplexSemimartingale.stochasticIntegral_of_zero_imaginary_part
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hi : Indistinguishable (fun t ω ↦ (Z t ω).im) 0 P) :
    Indistinguishable (hZ.stochasticIntegral hF ha hr)
      (hZ.1.complexIntegrandIntegral hF ha hr) P := by
  filter_upwards [hZ.2.complexIntegrandIntegral_eq_zero_of_integrator_eq_zero hF ha hr hi]
    with ω hI t
  change _ + Complex.I * _ = _
  rw [hI t]
  simp only [Pi.zero_apply, mul_zero, add_zero]

theorem IsComplexSemimartingale.stochasticIntegral_of_indistinguishable_real_integrator
    {Y : ℝ≥0 → Ω → ℝ}
    (hZ : IsComplexSemimartingale Z F P) (hY : IsSemimartingale Y F P)
    (hF : F.IsUsual P) (ha : Adapted F H) (hr : HasCagladPaths H P)
    (he : Indistinguishable Z (fun t ω ↦ (Y t ω : ℂ)) P) :
    Indistinguishable (hZ.stochasticIntegral hF ha hr)
      (hY.complexIntegrandIntegral hF ha hr) P := by
  have heR : Indistinguishable (fun t ω ↦ (Z t ω).re) Y P :=
    he.mono fun _ h t ↦ congrArg Complex.re (h t)
  have heI : Indistinguishable (fun t ω ↦ (Z t ω).im) 0 P :=
    he.mono fun _ h t ↦ congrArg Complex.im (h t)
  exact (hZ.stochasticIntegral_of_zero_imaginary_part hF ha hr heI).trans
    (hZ.1.complexIntegrandIntegral_congr_integrator hY hF ha hr heR)

end ProbabilityTheory
