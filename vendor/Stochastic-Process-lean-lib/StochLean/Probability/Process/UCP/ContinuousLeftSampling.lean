/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.LeftSampling
public import StochLean.Probability.Process.UCP.LeftContinuousDeviation
public import StochLean.Probability.Process.UCP.UniformConvergence

/-! # Random left sampling of continuous adapted processes

Random horizons tend to infinity and meshes tend to zero on one common event.
Actual compact pathwise convergence implies UCP convergence. This statement is
restricted to continuous paths; it is not used for jump-displaced step paths.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {π : ℕ → StoppingTimePartition F} {Y : ℝ≥0 → Ω → ℝ}

theorem IsTendingToIdentity.ae_locallyUniform_leftSample_of_continuous
    (hπ : IsTendingToIdentity π P) (hc : HasContinuousPaths Y P) :
    ∀ᵐ ω ∂P, ∀ T, TendstoUniformlyOn (fun n t ↦ (π n).leftSampleProcess Y t ω)
      (Y · ω) atTop (Icc 0 T) := by
  filter_upwards [hπ, hc] with ω hπω hY T
  apply StochLean.TimePartition.tendstoUniformlyOn_leftStep_of_eventually_le
    (fun n ↦ (π n).path ω) hY.continuousOn (hπω.1.eventually (eventually_ge_atTop T))
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hπω.2

theorem IsTendingToIdentity.tendstoUCP_leftSample_of_continuous [IsFiniteMeasure P]
    (hπ : IsTendingToIdentity π P) (ha : Adapted F Y) (hF : F.IsUsual P)
    (hc : HasContinuousPaths Y P) :
    TendstoUCP P (fun n ↦ (π n).leftSampleProcess Y) atTop Y := by
  apply tendstoUCP_of_ae_compactDeviation_of_aemeasurable
  · intro n T
    have hS := (π n).isSimplePredictable_leftSample_of_leftContinuous
      ha hF hc.hasLeftContinuousPaths
    exact aemeasurable_compactDeviation_of_leftContinuous
      (fun t ↦ (hS.adapted t).mono (F.le t) le_rfl)
      (fun t ↦ (ha t).mono (F.le t) le_rfl)
      (hS.hasCagladPaths P).hasLeftContinuousPaths hc.hasLeftContinuousPaths T
  · filter_upwards [hπ.ae_locallyUniform_leftSample_of_continuous hc] with ω hω T
    exact tendsto_compactDeviation_iff_tendstoUniformlyOn.mpr (hω T)

end ProbabilityTheory.StoppingTimePartition
