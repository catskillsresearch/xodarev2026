/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral

/-! # Linearity and integrand invariance of the constructed integral

Identities are indistinguishability statements, not equality of arbitrary chosen
versions. Every identity follows from actual simple approximations and uniqueness.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H K : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_congr_integrand
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) (hHK : Indistinguishable H K P) :
    Indistinguishable (hX.stochasticIntegral hF haH hrH)
      (hX.stochasticIntegral hF haK hrK) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP haH hF hrH
  exact hX.stochasticIntegral_indistinguishable_of_limit hF haH hrH hS huS
    (hX.tendstoUCP_stochasticIntegral_of_simple hF haK hrK hS (huS.congr_right hHK))
    (hX.hasCadlagPaths_stochasticIntegral hF haK hrK).hasRightContinuousPaths

theorem IsSemimartingale.stochasticIntegral_add
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    Indistinguishable
      (hX.stochasticIntegral hF (fun t ↦ (haH t).add (haK t)) (hrH.add hrK))
      (hX.stochasticIntegral hF haH hrH + hX.stochasticIntegral hF haK hrK) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP haH hF hrH
  obtain ⟨R, hR, huR⟩ := exists_simplePredictable_tendstoUCP haK hF hrK
  apply hX.stochasticIntegral_indistinguishable_of_limit hF _ _
    (fun n ↦ (hS n).add (hR n)) (huS.add huR)
  · have hsum := (hX.tendstoUCP_stochasticIntegral_of_simple hF haH hrH hS huS).add
      (hX.tendstoUCP_stochasticIntegral_of_simple hF haK hrK hR huR)
    have heq : (fun n ↦ ((hS n).add (hR n)).elementaryIntegralProcess X) =
        fun n ↦ (hS n).elementaryIntegralProcess X + (hR n).elementaryIntegralProcess X := by
      funext n
      exact (hS n).elementaryIntegralProcess_add (hR n) X
    rw [heq]
    exact hsum
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF haH hrH).add
      (hX.hasCadlagPaths_stochasticIntegral hF haK hrK)).hasRightContinuousPaths

theorem IsSemimartingale.stochasticIntegral_smul
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (c : ℝ) :
    Indistinguishable
      (hX.stochasticIntegral hF (fun t ↦ (ha t).const_mul c)
        (hr.continuous_comp (continuous_const.mul continuous_id)))
      (c • hX.stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply hX.stochasticIntegral_indistinguishable_of_limit hF _ _
    (fun n ↦ (hS n).smul c) (huS.smul c)
  · have hmul := (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).smul c
    have heq : (fun n ↦ ((hS n).smul c).elementaryIntegralProcess X) =
        fun n ↦ c • (hS n).elementaryIntegralProcess X := by
      funext n
      exact (hS n).elementaryIntegralProcess_smul c X
    rw [heq]
    exact hmul
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF ha hr).continuous_comp
      (continuous_const.mul continuous_id)).hasRightContinuousPaths

end ProbabilityTheory
