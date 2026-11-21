/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ClassificationStability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! # Accessible and totally inaccessible decomposition

Protter III.3 is obtained from Mathlib's countable essential union of measurable
sets: take all finite coincidence events with predictable stopping times.
Their essential union is accessible and the complementary finite event is
totally inaccessible. The argument works for s-finite measures and requires
neither usualness nor a competing stopping-time or predictable-time owner.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

/-- Source decomposition relation, specified before any existence theorem or selector. -/
structure IsAccessibleInaccessibleDecomposition (hτ : IsStoppingTime F τ) (P : Measure Ω)
    (A B : Set Ω) : Prop where
  measurable_left : MeasurableSet[hτ.measurableSpace] A
  measurable_right : MeasurableSet[hτ.measurableSpace] B
  disjoint : Disjoint A B
  union_ae : (A ∪ B : Set Ω) =ᵐ[P] {ω | τ ω ≠ ⊤}
  accessible : IsAccessibleStoppingTime F (restrictedStoppingTime τ A) P
  totallyInaccessible : IsTotallyInaccessibleStoppingTime F (restrictedStoppingTime τ B) P

theorem IsAccessibleInaccessibleDecomposition.reconstruct {hτ : IsStoppingTime F τ}
    {P : Measure Ω} {A B : Set Ω} (h : IsAccessibleInaccessibleDecomposition hτ P A B) :
    (fun ω ↦ min (restrictedStoppingTime τ A ω) (restrictedStoppingTime τ B ω)) =ᵐ[P] τ := by
  filter_upwards [h.union_ae] with ω hω
  change (ω ∈ A ∨ ω ∈ B) = (τ ω ≠ ⊤) at hω
  by_cases ht : τ ω = ⊤
  · simp only [restrictedStoppingTime, ht, ite_self, min_self]
  · rcases (Iff.of_eq hω).mpr ht with ha | hb
    · rw [restrictedStoppingTime_of_mem τ ha]
      exact min_eq_left (le_restrictedStoppingTime τ B ω)
    · rw [restrictedStoppingTime_of_mem τ hb]
      exact min_eq_right (le_restrictedStoppingTime τ A ω)

/-- Protter III.3 existence. The finite-graph restriction is essential in the
coincidence events and in the complementary event. -/
theorem exists_accessibleInaccessible_decomposition (hτ : IsStoppingTime F τ)
    (P : Measure Ω) [SFinite P] :
    ∃ A B : Set Ω, IsAccessibleInaccessibleDecomposition hτ P A B := by
  classical
  let C : Set (Set Ω) := {A | ∃ σ : Ω → WithTop ℝ≥0,
    IsPredictableStoppingTime F σ P ∧ A = {ω | τ ω = σ ω ∧ τ ω ≠ ⊤}}
  have hm (A : Set Ω) (hA : A ∈ C) : MeasurableSet[hτ.measurableSpace] A := by
    obtain ⟨σ, hσ, rfl⟩ := hA
    exact (hτ.measurableSet_eq_stopping_time hσ.1).inter
      (hτ.measurable (measurableSet_singleton ⊤)).compl
  obtain ⟨D, hDC, hDcount, hD⟩ := P.exists_ae_subset_biUnion_countable
    (fun A hA ↦ hτ.measurableSpace_le A (hm A hA))
  let A := ⋃₀ D
  let B := {ω | τ ω ≠ ⊤} \ A
  have hA : MeasurableSet[hτ.measurableSpace] A :=
    MeasurableSet.sUnion hDcount (fun E hE ↦ hm E (hDC hE))
  have hB : MeasurableSet[hτ.measurableSpace] B :=
    (hτ.measurable (measurableSet_singleton ⊤)).compl.diff hA
  have hAsub : A ⊆ {ω | τ ω ≠ ⊤} := by
    rintro ω ⟨E, hED, hωE⟩
    obtain ⟨σ, _, he⟩ := hDC hED
    rw [he] at hωE
    exact hωE.2
  obtain ⟨d, hd⟩ := (hDcount.insert ∅).exists_eq_range (insert_nonempty ∅ D)
  have hdn (n : ℕ) : ∃ σ : Ω → WithTop ℝ≥0,
      IsPredictableStoppingTime F σ P ∧ d n = {ω | τ ω = σ ω ∧ τ ω ≠ ⊤} := by
    have hmem : d n ∈ insert ∅ D := by rw [hd]; exact mem_range_self n
    rcases mem_insert_iff.mp hmem with he | hmem
    · refine ⟨fun _ ↦ ⊤, isPredictableStoppingTime_top F P, ?_⟩
      rw [he]
      ext ω
      simp
    · exact hDC hmem
  choose σ hσ hdσ using hdn
  have ha : IsAccessibleStoppingTime F (restrictedStoppingTime τ A) P := by
    refine ⟨hτ.restrictedStoppingTime hA, σ, hσ, Eventually.of_forall ?_⟩
    intro ω hf
    obtain ⟨hAω, _⟩ := (restrictedStoppingTime_ne_top_iff τ A ω).mp hf
    obtain ⟨E, hED, hωE⟩ := hAω
    have hmem : E ∈ insert ∅ D := mem_insert_of_mem _ hED
    rw [hd] at hmem
    obtain ⟨n, hn⟩ := hmem
    have he : τ ω = σ n ω := by
      rw [← hn, hdσ n] at hωE
      exact hωE.1
    exact ⟨n, (restrictedStoppingTime_of_mem τ (show ω ∈ A from ⟨E, hED, hωE⟩)).trans he⟩
  have ht : IsTotallyInaccessibleStoppingTime F (restrictedStoppingTime τ B) P := by
    refine ⟨hτ.restrictedStoppingTime hB, fun ρ hρ ↦ ?_⟩
    have hdom := hD {ω | τ ω = ρ ω ∧ τ ω ≠ ⊤} ⟨ρ, hρ, rfl⟩
    have hn : ∀ᵐ ω ∂P,
        ¬ (restrictedStoppingTime τ B ω = ρ ω ∧ restrictedStoppingTime τ B ω ≠ ⊤) := by
      filter_upwards [hdom] with ω hω
      rintro ⟨he, hf⟩
      obtain ⟨hBω, hτf⟩ := (restrictedStoppingTime_ne_top_iff τ B ω).mp hf
      have he' : τ ω = ρ ω := (restrictedStoppingTime_of_mem τ hBω).symm.trans he
      exact hBω.2 (hω ⟨he', hτf⟩)
    simpa only [not_not] using ae_iff.mp hn
  have hunion : A ∪ B = {ω | τ ω ≠ ⊤} := by
    ext ω
    change (ω ∈ A ∨ τ ω ≠ ⊤ ∧ ω ∉ A) ↔ τ ω ≠ ⊤
    constructor
    · exact fun hω ↦ hω.elim (fun ha ↦ hAsub ha) And.left
    · intro hf
      by_cases ha : ω ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨hf, ha⟩
  refine ⟨A, B, hA, hB, disjoint_left.mpr (fun _ ha hb ↦ hb.2 ha), ?_, ha, ht⟩
  exact Eventually.of_forall fun ω ↦ congrArg (fun E : Set Ω ↦ ω ∈ E) hunion

end ProbabilityTheory
