/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ClassificationDecomposition

/-! # Uniqueness of the accessible and totally inaccessible decomposition

Protter III.3 uniqueness is equality almost everywhere of both stopped-measurable
events and of both restricted stopping times. No selector is needed. The proof
uses the null finite intersection of an accessible and a totally inaccessible
graph, and works without a finiteness or completeness assumption on the measure.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {τ : Ω → WithTop ℝ≥0}

private theorem restricted_classes_disjoint_ae {A B : Set Ω}
    (ha : IsAccessibleStoppingTime F (restrictedStoppingTime τ A) P)
    (hb : IsTotallyInaccessibleStoppingTime F (restrictedStoppingTime τ B) P) :
    ∀ᵐ ω ∂P, ¬ (ω ∈ A ∧ ω ∈ B ∧ τ ω ≠ ⊤) := by
  rw [ae_iff]
  simpa only [not_not] using measure_mono_null (show
    {ω | ω ∈ A ∧ ω ∈ B ∧ τ ω ≠ ⊤} ⊆
      {ω | restrictedStoppingTime τ A ω = restrictedStoppingTime τ B ω ∧
        restrictedStoppingTime τ A ω ≠ ⊤} from by
    rintro ω ⟨hA, hB, hf⟩
    change restrictedStoppingTime τ A ω = restrictedStoppingTime τ B ω ∧
      restrictedStoppingTime τ A ω ≠ ⊤
    rw [restrictedStoppingTime_of_mem τ hA, restrictedStoppingTime_of_mem τ hB]
    exact ⟨rfl, hf⟩) (ha.measure_eq_of_totallyInaccessible hb)

theorem IsAccessibleInaccessibleDecomposition.events_unique {hτ : IsStoppingTime F τ}
    {A B A' B' : Set Ω} (h : IsAccessibleInaccessibleDecomposition hτ P A B)
    (h' : IsAccessibleInaccessibleDecomposition hτ P A' B') :
    A =ᵐ[P] A' ∧ B =ᵐ[P] B' := by
  have hn := restricted_classes_disjoint_ae h.accessible h'.totallyInaccessible
  have hn' := restricted_classes_disjoint_ae h'.accessible h.totallyInaccessible
  have hall : ∀ᵐ ω ∂P, (ω ∈ A ↔ ω ∈ A') ∧ (ω ∈ B ↔ ω ∈ B') := by
    filter_upwards [h.union_ae, h'.union_ae, hn, hn'] with ω hu hu' hne hne'
    change (ω ∈ A ∨ ω ∈ B) = (τ ω ≠ ⊤) at hu
    change (ω ∈ A' ∨ ω ∈ B') = (τ ω ≠ ⊤) at hu'
    have hu := Iff.of_eq hu
    have hu' := Iff.of_eq hu'
    constructor
    · constructor
      · intro ha
        have hf := hu.mp (Or.inl ha)
        rcases hu'.mpr hf with ha' | hb'
        · exact ha'
        · exact (hne ⟨ha, hb', hf⟩).elim
      · intro ha'
        have hf := hu'.mp (Or.inl ha')
        rcases hu.mpr hf with ha | hb
        · exact ha
        · exact (hne' ⟨ha', hb, hf⟩).elim
    · constructor
      · intro hb
        have hf := hu.mp (Or.inr hb)
        rcases hu'.mpr hf with ha' | hb'
        · exact (hne' ⟨ha', hb, hf⟩).elim
        · exact hb'
      · intro hb'
        have hf := hu'.mp (Or.inr hb')
        rcases hu.mpr hf with ha | hb
        · exact (hne ⟨ha, hb', hf⟩).elim
        · exact hb
  exact ⟨hall.mono (fun _ hω ↦ propext hω.1), hall.mono (fun _ hω ↦ propext hω.2)⟩

theorem IsAccessibleInaccessibleDecomposition.times_unique {hτ : IsStoppingTime F τ}
    {A B A' B' : Set Ω} (h : IsAccessibleInaccessibleDecomposition hτ P A B)
    (h' : IsAccessibleInaccessibleDecomposition hτ P A' B') :
    restrictedStoppingTime τ A =ᵐ[P] restrictedStoppingTime τ A' ∧
      restrictedStoppingTime τ B =ᵐ[P] restrictedStoppingTime τ B' := by
  classical
  obtain ⟨ha, hb⟩ := h.events_unique h'
  constructor
  · filter_upwards [ha] with ω hω
    change (ω ∈ A) = (ω ∈ A') at hω
    simp only [restrictedStoppingTime, hω]
  · filter_upwards [hb] with ω hω
    change (ω ∈ B) = (ω ∈ B') at hω
    simp only [restrictedStoppingTime, hω]

/-- Full Protter III.3: existence, reconstruction, and almost-sure uniqueness
of the events and the two restricted stopping times. -/
theorem exists_unique_accessibleInaccessible_decomposition (hτ : IsStoppingTime F τ)
    (P : Measure Ω) [SFinite P] :
    ∃ A B : Set Ω, IsAccessibleInaccessibleDecomposition hτ P A B ∧
      (fun ω ↦ min (restrictedStoppingTime τ A ω) (restrictedStoppingTime τ B ω)) =ᵐ[P] τ ∧
      ∀ A' B', IsAccessibleInaccessibleDecomposition hτ P A' B' →
        (A =ᵐ[P] A' ∧ B =ᵐ[P] B') ∧
          (restrictedStoppingTime τ A =ᵐ[P] restrictedStoppingTime τ A' ∧
            restrictedStoppingTime τ B =ᵐ[P] restrictedStoppingTime τ B') := by
  obtain ⟨A, B, h⟩ := exists_accessibleInaccessible_decomposition hτ P
  exact ⟨A, B, h, h.reconstruct, fun _ _ h' ↦ ⟨h.events_unique h', h.times_unique h'⟩⟩

end ProbabilityTheory
