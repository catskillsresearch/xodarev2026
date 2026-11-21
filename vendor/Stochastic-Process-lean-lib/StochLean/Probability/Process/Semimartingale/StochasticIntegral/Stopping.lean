/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.Stopping
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessStopping
public import StochLean.Probability.Process.UCP.Stopping

/-! # Protter II.12: stopping the constructed Chapter II integral

Stopping the integral, stopping its integrator, and cutting off the integrand
on the closed stochastic interval give indistinguishable processes. The proof
passes the actual source identities through UCP convergence and uniqueness.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_stoppedProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable ((hX.stoppedProcess hF hτ).stochasticIntegral hF ha hr)
      (MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply (hX.stoppedProcess hF hτ).stochasticIntegral_indistinguishable_of_limit
    hF ha hr hS huS
  · have heq : (fun n ↦ (hS n).elementaryIntegralProcess (MeasureTheory.stoppedProcess X τ)) =
        fun n ↦ MeasureTheory.stoppedProcess ((hS n).elementaryIntegralProcess X) τ := by
      funext n
      exact (hS n).elementaryIntegralProcess_stoppedProcess X τ
    rw [heq]
    exact (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).stoppedProcess τ
  · exact (hX.hasCadlagPaths_stochasticIntegral hF ha hr).hasRightContinuousPaths.stoppedProcess τ

theorem IsSemimartingale.stochasticIntegral_cutoff
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (hX.stochasticIntegral hF (adapted_cutoffIntegrand ha hτ) (hr.cutoffIntegrand τ))
      (MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply hX.stochasticIntegral_indistinguishable_of_limit hF _ _
    (fun n ↦ (hS n).cutoff hτ) (huS.cutoffIntegrand τ)
  · have heq : (fun n ↦ ((hS n).cutoff hτ).elementaryIntegralProcess X) =
        fun n ↦ MeasureTheory.stoppedProcess ((hS n).elementaryIntegralProcess X) τ := by
      funext n
      exact (hS n).elementaryIntegralProcess_cutoff hτ X
    rw [heq]
    exact (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).stoppedProcess τ
  · exact (hX.hasCadlagPaths_stochasticIntegral hF ha hr).hasRightContinuousPaths.stoppedProcess τ

theorem IsSemimartingale.stochasticIntegral_cutoff_eq_stoppedIntegrator
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (hX.stochasticIntegral hF (adapted_cutoffIntegrand ha hτ) (hr.cutoffIntegrand τ))
      ((hX.stoppedProcess hF hτ).stochasticIntegral hF ha hr) P :=
  (hX.stochasticIntegral_cutoff hF ha hr hτ).trans
    (hX.stochasticIntegral_stoppedProcess hF ha hr hτ).symm

end ProbabilityTheory
