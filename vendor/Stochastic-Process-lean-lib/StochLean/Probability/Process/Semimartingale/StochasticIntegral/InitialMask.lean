/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Stopping
public import StochLean.Probability.Process.Semimartingale.InitialMask
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.InitialMask
public import StochLean.Probability.Process.UCP.InitialMask

/-! # Initial masks commute with the constructed stochastic integral

The source initial term is included in both identities. Combining the identities
with stopping gives the exact masked local-property convention.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_indicator_integrand
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Indistinguishable
      (hX.stochasticIntegral hF (ha.indicator_initial hs) (hr.indicator s))
      (fun t ↦ s.indicator (hX.stochasticIntegral hF ha hr t)) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply hX.stochasticIntegral_indistinguishable_of_limit hF _ _
    (fun n ↦ (hS n).indicator hs) (huS.indicator s)
  · have heq : (fun n ↦ ((hS n).indicator hs).elementaryIntegralProcess X) =
        fun n t ↦ s.indicator ((hS n).elementaryIntegralProcess X t) := by
      funext n
      exact (hS n).elementaryIntegralProcess_indicator hs X
    rw [heq]
    exact (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).indicator s
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF ha hr).indicator s).hasRightContinuousPaths

theorem IsSemimartingale.stochasticIntegral_indicator_integrator
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Indistinguishable ((hX.indicator_initial hs).stochasticIntegral hF ha hr)
      (fun t ↦ s.indicator (hX.stochasticIntegral hF ha hr t)) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply (hX.indicator_initial hs).stochasticIntegral_indistinguishable_of_limit hF ha hr hS huS
  · simp only [IsSimplePredictable.elementaryIntegralProcess_indicator_integrator]
    exact (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).indicator s
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF ha hr).indicator s).hasRightContinuousPaths

theorem IsSemimartingale.stochasticIntegral_masked_cutoff
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (hX.stochasticIntegral hF
        ((adapted_cutoffIntegrand ha hτ).indicator_initial (hτ.measurableSet_gt 0))
        ((hr.cutoffIntegrand τ).indicator {ω | 0 < τ ω}))
      (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ ω}.indicator (hX.stochasticIntegral hF ha hr t)) τ) P := by
  rw [stoppedProcess_indicator_comm']
  exact (hX.stochasticIntegral_indicator_integrand hF (adapted_cutoffIntegrand ha hτ)
    (hr.cutoffIntegrand τ) (hτ.measurableSet_gt 0)).trans
    ((hX.stochasticIntegral_cutoff hF ha hr hτ).indicator {ω | 0 < τ ω})

theorem IsSemimartingale.stochasticIntegral_masked_stoppedProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (((hX.indicator_initial (hτ.measurableSet_gt 0)).stoppedProcess hF hτ).stochasticIntegral
        hF ha hr)
      (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ ω}.indicator (hX.stochasticIntegral hF ha hr t)) τ) P :=
  ((hX.indicator_initial (hτ.measurableSet_gt 0)).stochasticIntegral_stoppedProcess
    hF ha hr hτ).trans
    ((hX.stochasticIntegral_indicator_integrator hF ha hr (hτ.measurableSet_gt 0)).stoppedProcess τ)

end ProbabilityTheory
