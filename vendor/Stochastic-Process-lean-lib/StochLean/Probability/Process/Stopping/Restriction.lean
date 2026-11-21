/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Graph

/-! # Restricting a stopping time to an event

Protter III.2's `T_A` is `T` on `A` and infinity off `A`. Stopping requires
`A ∈ F_T`, not initial measurability. The graph restriction is an exact
finite-time identity, including the zero-time section.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*}

noncomputable def restrictedStoppingTime (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    Ω → WithTop ℝ≥0 := by
  classical
  exact fun ω ↦ if ω ∈ A then τ ω else ⊤

theorem restrictedStoppingTime_of_mem (τ : Ω → WithTop ℝ≥0) {A : Set Ω}
    {ω : Ω} (hω : ω ∈ A) : restrictedStoppingTime τ A ω = τ ω := by
  simp only [restrictedStoppingTime, if_pos hω]

theorem restrictedStoppingTime_of_notMem (τ : Ω → WithTop ℝ≥0) {A : Set Ω}
    {ω : Ω} (hω : ω ∉ A) : restrictedStoppingTime τ A ω = ⊤ := by
  simp only [restrictedStoppingTime, if_neg hω]

theorem restrictedStoppingTime_ne_top_iff (τ : Ω → WithTop ℝ≥0) (A : Set Ω) (ω : Ω) :
    restrictedStoppingTime τ A ω ≠ ⊤ ↔ ω ∈ A ∧ τ ω ≠ ⊤ := by
  by_cases hω : ω ∈ A <;> simp [restrictedStoppingTime, hω]

@[simp] theorem restrictedStoppingTime_univ (τ : Ω → WithTop ℝ≥0) :
    restrictedStoppingTime τ univ = τ := by
  funext ω
  exact restrictedStoppingTime_of_mem τ (mem_univ ω)

@[simp] theorem restrictedStoppingTime_empty (τ : Ω → WithTop ℝ≥0) :
    restrictedStoppingTime τ ∅ = fun _ ↦ ⊤ := by
  funext ω
  exact restrictedStoppingTime_of_notMem τ (notMem_empty ω)

theorem le_restrictedStoppingTime (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    τ ≤ restrictedStoppingTime τ A := by
  intro ω
  by_cases hω : ω ∈ A
  · rw [restrictedStoppingTime_of_mem τ hω]
  · rw [restrictedStoppingTime_of_notMem τ hω]
    exact le_top

theorem restrictedStoppingTime_inter (τ : Ω → WithTop ℝ≥0) (A B : Set Ω) :
    restrictedStoppingTime (restrictedStoppingTime τ A) B = restrictedStoppingTime τ (A ∩ B) := by
  funext ω
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [restrictedStoppingTime, ha, hb]

theorem min_restrictedStoppingTime_compl (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    (fun ω ↦ min (restrictedStoppingTime τ A ω) (restrictedStoppingTime τ Aᶜ ω)) = τ := by
  funext ω
  by_cases ha : ω ∈ A <;> simp [restrictedStoppingTime, ha]

theorem stoppingTimeGraph_restricted (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    stoppingTimeGraph (restrictedStoppingTime τ A) = stoppingTimeGraph τ ∩ (univ ×ˢ A) := by
  ext ⟨t, ω⟩
  by_cases hω : ω ∈ A
  · simp [restrictedStoppingTime, hω]
  · simp only [mem_stoppingTimeGraph, restrictedStoppingTime, hω, ↓reduceIte,
      ENNReal.some_eq_coe', mem_inter_iff, mem_prod, mem_univ, and_false, iff_false]
    exact WithTop.top_ne_coe

end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem restrictedStoppingTime (hτ : IsStoppingTime F τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    IsStoppingTime F (ProbabilityTheory.restrictedStoppingTime τ A) := by
  intro t
  have he : {ω | ProbabilityTheory.restrictedStoppingTime τ A ω ≤ t} =
      A ∩ {ω | τ ω ≤ t} := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [ProbabilityTheory.restrictedStoppingTime, hω]
    · simp only [ProbabilityTheory.restrictedStoppingTime, ENNReal.some_eq_coe',
        mem_ofPred_eq, hω, ↓reduceIte, mem_inter_iff, false_and, iff_false]
      exact WithTop.not_top_le_coe t
  rw [he]
  exact hA.2 t

end MeasureTheory.IsStoppingTime
