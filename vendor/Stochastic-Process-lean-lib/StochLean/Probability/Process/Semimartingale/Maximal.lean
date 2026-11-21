/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessRegularity
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessStopping
public import StochLean.Probability.Process.Stopping.FirstExitMaximal

/-! # The source elementary integral maximal estimate

This is the uniform-input step in Protter II.11. A total good integrator controls
the entire elementary integral process on each compact horizon by applying the
existing terminal estimate to the simple integrand cut off at a finite first exit.
It does not yet assume or prove UCP density, completeness or a general integral.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem IsTotalSemimartingale.elementaryIntegralProcess_maximal_uniform
    (hX : IsTotalSemimartingale X F P) (hF : F.IsUsual P)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ≥0 → Ω → ℝ,
      ∀ hH : IsSimplePredictable H F, (∀ t ω, ‖H t ω‖ ≤ δ) → ∀ T : ℝ≥0,
      P {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ≤ η := by
  obtain ⟨δ, hδ, hb⟩ := (isGoodIntegrator_iff_continuousAtZero.mp hX.2.2) ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound T ↦ ?_⟩
  let Y := hH.elementaryIntegralProcess X
  have hrY : HasRightContinuousPaths Y P :=
    (hH.hasCadlagPaths_elementaryIntegralProcess hX.2.1).hasRightContinuousPaths
  have haY : Adapted F Y := hH.adapted_elementaryIntegralProcess hX.1 hF
    hX.2.1.hasRightContinuousPaths
  have hτ := haY.isStoppingTime_hittingAfter_norm_of_usual hF hrY ε
  let σ := FiniteStoppingTime.truncate hτ T
  have hσ : IsStoppingTime F σ.withTop := σ.isStoppingTime
  have hsize : ∀ t ω, ‖cutoffIntegrand H σ.withTop t ω‖ ≤ δ := by
    intro t ω
    simp only [cutoffIntegrand]
    split_ifs
    · exact hbound t ω
    · simpa only [norm_zero] using hδ.le
  have hi := hb _ (hH.cutoff hσ) hsize
  have heq (ω : Ω) : (hH.cutoff hσ).elementaryIntegral X ω =
      stoppedProcess Y (hittingAfter Y {x | ε < ‖x‖} 0) T ω := by
    rw [hH.elementaryIntegral_cutoff hσ X,
      hH.elementaryIntegral_stoppedFinite_eq_elementaryIntegralProcess X σ]
    rfl
  calc
    _ ≤ P {ω | ε ≤ ‖stoppedProcess Y (hittingAfter Y {x | ε < ‖x‖} 0) T ω‖} :=
      measure_exists_norm_lt_le_firstExit_stopped hrY ε T
    _ = P {ω | ε ≤ ‖(hH.cutoff hσ).elementaryIntegral X ω‖} := by simp only [heq]
    _ ≤ η := hi

theorem IsSemimartingale.elementaryIntegralProcess_maximal_uniform
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (T : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ≥0 → Ω → ℝ,
      ∀ hH : IsSimplePredictable H F, (∀ t ω, ‖H t ω‖ ≤ δ) →
      P {ω | ∃ t ≤ T, ε < ‖hH.elementaryIntegralProcess X t ω‖} ≤ η := by
  obtain ⟨δ, hδ, hb⟩ := (hX T).elementaryIntegralProcess_maximal_uniform hF ε hε η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  apply le_trans (measure_mono ?_) (hb H hH hbound T)
  rintro ω ⟨t, ht, hω⟩
  refine ⟨t, ht, ?_⟩
  rw [hH.elementaryIntegralProcess_stoppedProcess,
    stoppedProcess_eq_of_le (τ := fun _ : Ω ↦ (T : WithTop ℝ≥0))
      (ω := ω) (WithTop.coe_le_coe.mpr ht)]
  exact hω

end ProbabilityTheory
