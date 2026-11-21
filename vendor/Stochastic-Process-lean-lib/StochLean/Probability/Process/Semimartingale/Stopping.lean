/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Stopping
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual

/-! # Stopping source good integrators and semimartingales

The good-integrator proof uses actual source cutoff closure and elementary stopping,
not a classical semimartingale decomposition or a postulated general integral.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem IsGoodIntegrator.stoppedProcess (hX : IsGoodIntegrator X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsGoodIntegrator (MeasureTheory.stoppedProcess X τ) F P := by
  apply isGoodIntegrator_iff_continuousAtZero.mpr
  intro ε hε η hη
  obtain ⟨δ, hδ, hb⟩ := (isGoodIntegrator_iff_continuousAtZero.mp hX) ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  rw [← hH.elementaryIntegral_cutoff hτ]
  apply hb (cutoffIntegrand H τ) (hH.cutoff hτ)
  intro t ω
  by_cases ht : (t : WithTop ℝ≥0) ≤ τ ω
  · simpa only [cutoffIntegrand, if_pos ht] using hbound t ω
  · simpa only [cutoffIntegrand, if_neg ht, norm_zero] using hδ.le

theorem IsTotalSemimartingale.stoppedProcess_of_adapted (hX : IsTotalSemimartingale X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (ha : Adapted F (MeasureTheory.stoppedProcess X τ)) :
    IsTotalSemimartingale (MeasureTheory.stoppedProcess X τ) F P :=
  ⟨ha, hX.2.1.stoppedProcess τ, hX.2.2.stoppedProcess hτ⟩

theorem IsTotalSemimartingale.stoppedProcess (hX : IsTotalSemimartingale X F P)
    (hF : F.IsUsual P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsTotalSemimartingale (MeasureTheory.stoppedProcess X τ) F P :=
  hX.stoppedProcess_of_adapted hτ
    (hX.1.stronglyAdapted.stoppedProcess_of_usual hF hX.2.1.hasRightContinuousPaths hτ).adapted

/-- A total semimartingale is ordinary; deterministic stopping needs no usual conditions. -/
theorem IsTotalSemimartingale.isSemimartingale (hX : IsTotalSemimartingale X F P) :
    IsSemimartingale X F P := by
  intro T
  apply hX.stoppedProcess_of_adapted (isStoppingTime_const F T)
  intro t
  change Measurable[F t] (X (min t T))
  exact (hX.1 _).mono (F.mono (min_le_left t T)) le_rfl

theorem IsSemimartingale.stoppedProcess (hX : IsSemimartingale X F P)
    (hF : F.IsUsual P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsSemimartingale (MeasureTheory.stoppedProcess X τ) F P := by
  intro T
  have h := (hX T).stoppedProcess hF hτ
  simpa only [stoppedProcess_stoppedProcess, inf_comm] using h

theorem IsSemimartingale.isTotalSemimartingale_stopped_of_le
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) :
    IsTotalSemimartingale (MeasureTheory.stoppedProcess X τ) F P := by
  have h := (hX T).stoppedProcess hF hτ
  simpa only [stoppedProcess_stoppedProcess_of_le_right hbound] using h

end ProbabilityTheory
