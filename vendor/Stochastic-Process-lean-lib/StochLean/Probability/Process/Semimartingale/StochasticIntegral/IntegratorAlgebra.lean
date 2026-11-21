/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Subtraction
public import StochLean.Probability.Process.Semimartingale.Subtraction
public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessIntegratorAlgebra

/-! # Linearity of the constructed integral in the semimartingale integrator

Every identity compares the existing canonical selectors by indistinguishability.
One common simple approximation suffices for both integrators; no convergence
of arbitrary varying semimartingales is asserted.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_add_integrator
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable ((hX.add hY).stochasticIntegral hF ha hr)
      (hX.stochasticIntegral hF ha hr + hY.stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply (hX.add hY).stochasticIntegral_indistinguishable_of_limit hF ha hr hS huS
  · have hu := (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).add
      (hY.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS)
    simpa only [IsSimplePredictable.elementaryIntegralProcess_add_integrator] using hu
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF ha hr).add
      (hY.hasCadlagPaths_stochasticIntegral hF ha hr)).hasRightContinuousPaths

theorem IsSemimartingale.stochasticIntegral_const_mul_integrator
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (c : ℝ) :
    Indistinguishable ((hX.const_mul c).stochasticIntegral hF ha hr)
      (c • hX.stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply (hX.const_mul c).stochasticIntegral_indistinguishable_of_limit hF ha hr hS huS
  · have hu := (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).smul c
    simpa only [IsSimplePredictable.elementaryIntegralProcess_const_mul_integrator] using hu
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF ha hr).continuous_comp
      (continuous_const.mul continuous_id)).hasRightContinuousPaths

theorem IsSemimartingale.stochasticIntegral_sub_integrator
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable ((hX.sub hY).stochasticIntegral hF ha hr)
      (hX.stochasticIntegral hF ha hr - hY.stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply (hX.sub hY).stochasticIntegral_indistinguishable_of_limit hF ha hr hS huS
  · have hu := (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).sub
      (hY.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS)
    simpa only [IsSimplePredictable.elementaryIntegralProcess_sub_integrator] using hu
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF ha hr).sub
      (hY.hasCadlagPaths_stochasticIntegral hF ha hr)).hasRightContinuousPaths

end ProbabilityTheory
