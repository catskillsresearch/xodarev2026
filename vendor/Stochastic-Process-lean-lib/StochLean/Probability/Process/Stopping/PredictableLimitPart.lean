/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PredictableRestriction
public import StochLean.Probability.Process.Stopping.Supremum
public import StochLean.Probability.Process.Stopping.Classification

/-! # The predictable strict-limit part of increasing stopping times

An increasing sequence need not announce its limit everywhere. Restricting
the limit to the event where every term is strictly smaller does give a
predictable time. In particular a totally inaccessible finite time cannot
coincide with such a strict limit on a non-null event. This is a stopping-time
prerequisite in Protter III.10's conditional jump estimate.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {σ : ℕ → Ω → WithTop ℝ≥0}

theorem isPredictableStoppingTime_iSup_restricted_strict
    (hσ : ∀ n, IsStoppingTime F (σ n)) (hm : ∀ ω, Monotone (fun n ↦ σ n ω))
    (hF : F.IsUsual P) :
    IsPredictableStoppingTime F
      (restrictedStoppingTime (fun ω ↦ ⨆ n, σ n ω) {ω | ∀ n, σ n ω < ⨆ k, σ k ω}) P := by
  let τ : Ω → WithTop ℝ≥0 := fun ω ↦ ⨆ n, σ n ω
  let A : Set Ω := {ω | ∀ n, σ n ω < τ ω}
  have hτ : IsStoppingTime F τ := IsStoppingTime.iSup_nnreal hσ
  let G := F.stoppingTimeReindex σ hσ (fun _ _ hij ω ↦ hm ω hij)
  have hAbefore : MeasurableSet[hτ.measurableSpaceBefore] A := by
    have he : A = ⋂ n, {ω | σ n ω < τ ω} := by ext ω; simp only [A, mem_iInter, mem_ofPred_eq]
    rw [he]
    exact MeasurableSet.iInter fun n ↦ (hσ n).measurableSet_lt_before hτ
  have hAG : MeasurableSet[⨆ n, G n] A := by
    have he : A = ⋂ n, ⋃ m, {ω | σ n ω < σ m ω} := by
      ext ω
      simp only [A, τ, mem_ofPred_eq, mem_iInter, mem_iUnion, lt_iSup_iff]
    rw [he]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iUnion
    intro m
    apply le_iSup (fun k ↦ G k) m
    have he : {ω | σ n ω < σ m ω} = {ω | σ m ω ≤ σ n ω}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    rw [he]
    exact ((hσ m).measurableSet_le_stopping_time (hσ n)).compl
  obtain ⟨B, hB, hBA⟩ := G.exists_measurableSet_eventually_iff (P := P) hAG
  exact isPredictableStoppingTime_restricted_of_eventual_events hσ hm
    (Eventually.of_forall fun ω ↦ tendsto_atTop_iSup (hm ω)) hτ hF
    (hτ.measurableSpaceBefore_le A hAbefore) (fun n _ hω _ ↦ hω n) hB hBA

theorem IsTotallyInaccessibleStoppingTime.measure_strict_iSup_eq_zero
    {τ : Ω → WithTop ℝ≥0} (ht : IsTotallyInaccessibleStoppingTime F τ P)
    (hσ : ∀ n, IsStoppingTime F (σ n)) (hm : ∀ ω, Monotone (fun n ↦ σ n ω))
    (hF : F.IsUsual P) :
    P {ω | (⨆ n, σ n ω) = τ ω ∧ τ ω ≠ ⊤ ∧ ∀ n, σ n ω < τ ω} = 0 := by
  have hp := isPredictableStoppingTime_iSup_restricted_strict hσ hm hF
  apply measure_mono_null _ (ht.2 _ hp)
  rintro ω ⟨he, hf, hs⟩
  have hA : ω ∈ {ω | ∀ n, σ n ω < ⨆ k, σ k ω} := by
    change ∀ n, σ n ω < ⨆ k, σ k ω
    rw [he]
    exact hs
  refine ⟨?_, hf⟩
  rw [restrictedStoppingTime_of_mem _ hA]
  exact he.symm

end ProbabilityTheory
