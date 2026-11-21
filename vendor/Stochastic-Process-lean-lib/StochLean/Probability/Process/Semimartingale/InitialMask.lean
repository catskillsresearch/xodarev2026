/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegratorInitialMask
public import StochLean.Probability.Process.Measurability.InitialMask

/-! # Initial-event masks preserve source semimartingales

The good-integrator estimate is a direct outer-measure contraction. Adaptedness
uses only measurability of the event at time zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem IsGoodIntegrator.indicator (hX : IsGoodIntegrator X F P) (s : Set Ω) :
    IsGoodIntegrator (fun t ↦ s.indicator (X t)) F P := by
  apply isGoodIntegrator_iff_continuousAtZero.mpr
  intro ε hε η hη
  obtain ⟨δ, hδ, hb⟩ := isGoodIntegrator_iff_continuousAtZero.mp hX ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  apply le_trans (measure_mono ?_) (hb H hH hbound)
  intro ω hω
  rw [hH.elementaryIntegral_indicator_integrator X s] at hω
  change ε ≤ ‖s.indicator (hH.elementaryIntegral X) ω‖ at hω
  change ε ≤ ‖hH.elementaryIntegral X ω‖
  by_cases hs : ω ∈ s
  · simpa only [indicator_of_mem hs] using hω
  · simp only [indicator_of_notMem hs, norm_zero] at hω
    exact (not_le_of_gt hε hω).elim

theorem IsTotalSemimartingale.indicator_initial (hX : IsTotalSemimartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsTotalSemimartingale (fun t ↦ s.indicator (X t)) F P :=
  ⟨hX.1.indicator_initial hs, hX.2.1.indicator s, hX.2.2.indicator s⟩

theorem IsSemimartingale.indicator_initial (hX : IsSemimartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsSemimartingale (fun t ↦ s.indicator (X t)) F P := by
  intro t
  rw [stoppedProcess_indicator_comm']
  exact (hX t).indicator_initial hs

end ProbabilityTheory
