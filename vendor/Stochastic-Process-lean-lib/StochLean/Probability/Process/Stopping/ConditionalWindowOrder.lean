/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalWindow

/-! # Version-independent order of conditional stopping windows

Any cadlag versions of nested conditional stopping windows are ordered on
one common full-measure event, simultaneously at all times. The proof does
not require a prior choice of jointly ordered conditional representatives.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
  {δ ε : ℝ≥0} {R S : ℝ≥0 → Ω → ℝ}

theorem cadlag_conditional_window_ae_le (hτ : IsStoppingTime F τ) (hδε : δ ≤ ε)
    (hrR : HasRightContinuousPaths R P) (hrS : HasRightContinuousPaths S P)
    (heR : ∀ t : ℝ≥0, R t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t])
    (heS : ∀ t : ℝ≥0, S t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + ε : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) :
    ∀ᵐ ω ∂P, ∀ t, R t ω ≤ S t ω := by
  apply hrR.ae_forall_le_of_forall_ae_le hrS
  intro t
  have hi (c : ℝ≥0) : Integrable
      ({ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + c : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator
      ((F.le t _ (hτ.measurableSet_gt t)).inter (F.le (t + c) _ (hτ (t + c))))
  have hle := condExp_mono (m := F t) (hi δ) (hi ε) (Eventually.of_forall fun ω ↦ by
    have hsub : ((t + δ : ℝ≥0) : WithTop ℝ≥0) ≤ (t + ε : ℝ≥0) :=
      WithTop.coe_le_coe.mpr (add_le_add le_rfl hδε)
    simp only [indicator_apply, mem_ofPred_eq]
    by_cases hδ : (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)
    · have hε := And.intro hδ.1 (hδ.2.trans hsub)
      simp only [hδ, hε, le_refl]
    · rw [if_neg hδ]
      split_ifs <;> norm_num)
  exact (heR t).trans_le (hle.trans_eq (heS t).symm)

omit [IsFiniteMeasure P] in
theorem cadlag_conditional_window_unique
    (hrR : HasRightContinuousPaths R P) (hrS : HasRightContinuousPaths S P)
    (heR : ∀ t : ℝ≥0, R t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t])
    (heS : ∀ t : ℝ≥0, S t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) : Indistinguishable R S P := by
  have hm : IsModification R S P := fun t ↦ (heR t).trans (heS t).symm
  exact hm.indistinguishable_of_rightContinuous hrR hrS

omit [IsFiniteMeasure P] in
theorem cadlag_conditional_window_zero_delay
    (hrR : HasRightContinuousPaths R P)
    (heR : ∀ t : ℝ≥0, R t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + 0 : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) : Indistinguishable R 0 P := by
  have he (t : ℝ≥0) : R t =ᵐ[P] 0 := by
    have hempty : {ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + 0 : ℝ≥0) : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [add_zero, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h ↦ (not_lt_of_ge h.2) h.1
    have h := heR t
    rw [hempty, indicator_empty] at h
    change R t =ᵐ[P] P[(0 : Ω → ℝ) | F t] at h
    simpa only [condExp_zero] using h
  exact (show IsModification R 0 P from he).indistinguishable_of_rightContinuous hrR
    (Eventually.of_forall fun _ _ ↦ continuousWithinAt_const)

end MeasureTheory
