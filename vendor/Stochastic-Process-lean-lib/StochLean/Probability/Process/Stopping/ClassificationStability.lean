/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Classification

/-! # Restriction stability and disjointness of the two stopping classes

An accessible finite graph and a totally inaccessible finite graph have null
intersection. Both classes are preserved by restriction to a stopped-measurable
event. This does not claim that such restriction preserves predictability.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {τ σ : Ω → WithTop ℝ≥0}

theorem IsAccessibleStoppingTime.measure_eq_of_totallyInaccessible
    (ha : IsAccessibleStoppingTime F τ P) (ht : IsTotallyInaccessibleStoppingTime F σ P) :
    P {ω | τ ω = σ ω ∧ τ ω ≠ ⊤} = 0 := by
  obtain ⟨ρ, hρ, hcover⟩ := ha.2
  have hnull (n : ℕ) : ∀ᵐ ω ∂P, ¬ (σ ω = ρ n ω ∧ σ ω ≠ ⊤) := by
    rw [ae_iff]
    simpa only [not_not] using ht.2 (ρ n) (hρ n)
  have hne : ∀ᵐ ω ∂P, ¬ (τ ω = σ ω ∧ τ ω ≠ ⊤) := by
    filter_upwards [hcover, ae_all_iff.mpr hnull] with ω hω hn
    rintro ⟨he, hf⟩
    obtain ⟨n, he'⟩ := hω hf
    exact hn n ⟨he.symm.trans he', he ▸ hf⟩
  simpa only [not_not] using ae_iff.mp hne

theorem IsAccessibleStoppingTime.restrictedStoppingTime
    (ha : IsAccessibleStoppingTime F τ P) {A : Set Ω}
    (hA : MeasurableSet[ha.1.measurableSpace] A) :
    IsAccessibleStoppingTime F (restrictedStoppingTime τ A) P := by
  obtain ⟨ρ, hρ, hcover⟩ := ha.2
  refine ⟨ha.1.restrictedStoppingTime hA, ρ, hρ, ?_⟩
  filter_upwards [hcover] with ω hω hf
  obtain ⟨hAω, ht⟩ := (restrictedStoppingTime_ne_top_iff τ A ω).mp hf
  obtain ⟨n, hn⟩ := hω ht
  exact ⟨n, (restrictedStoppingTime_of_mem τ hAω).trans hn⟩

theorem IsTotallyInaccessibleStoppingTime.restrictedStoppingTime
    (ht : IsTotallyInaccessibleStoppingTime F τ P) {A : Set Ω}
    (hA : MeasurableSet[ht.1.measurableSpace] A) :
    IsTotallyInaccessibleStoppingTime F (restrictedStoppingTime τ A) P := by
  refine ⟨ht.1.restrictedStoppingTime hA, fun σ hσ ↦ ?_⟩
  refine measure_mono_null ?_ (ht.2 σ hσ)
  intro ω hω
  obtain ⟨hAω, hf⟩ := (restrictedStoppingTime_ne_top_iff τ A ω).mp hω.2
  exact ⟨(restrictedStoppingTime_of_mem τ hAω).symm.trans hω.1, hf⟩

end ProbabilityTheory
