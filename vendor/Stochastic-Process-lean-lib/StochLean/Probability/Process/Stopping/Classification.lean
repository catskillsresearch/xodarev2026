/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingExamples
public import StochLean.Probability.Process.Stopping.Restriction

/-! # Accessible and totally inaccessible stopping times

Protter III.2 uses countable predictable coverage of the finite graph for
accessibility and null intersection with every predictable finite graph for
total inaccessibility. The almost-sure coverage formulation also works for
arbitrary measures. Infinite times are excluded from all coincidence tests.

These predicates and their elementary consequences do not by themselves prove
the general accessible/totally-inaccessible decomposition of Protter III.3.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Countably many predictable stopping times cover the finite graph almost surely. -/
def IsAccessibleStoppingTime (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (P : Measure Ω) : Prop :=
  IsStoppingTime F τ ∧ ∃ σ : ℕ → Ω → WithTop ℝ≥0,
    (∀ n, IsPredictableStoppingTime F (σ n) P) ∧
      ∀ᵐ ω ∂P, τ ω ≠ ⊤ → ∃ n, τ ω = σ n ω

/-- Every predictable finite graph meets this graph on a null event. -/
def IsTotallyInaccessibleStoppingTime (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (P : Measure Ω) : Prop :=
  IsStoppingTime F τ ∧ ∀ σ : Ω → WithTop ℝ≥0, IsPredictableStoppingTime F σ P →
    P {ω | τ ω = σ ω ∧ τ ω ≠ ⊤} = 0

variable {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {P : Measure Ω}

theorem IsPredictableStoppingTime.isAccessible (h : IsPredictableStoppingTime F τ P) :
    IsAccessibleStoppingTime F τ P :=
  ⟨h.1, fun _ ↦ τ, fun _ ↦ h, Eventually.of_forall fun _ _ ↦ ⟨0, rfl⟩⟩

theorem isAccessibleStoppingTime_of_ae_eq_top (hτ : IsStoppingTime F τ)
    (h : τ =ᵐ[P] (fun _ ↦ ⊤)) : IsAccessibleStoppingTime F τ P := by
  refine ⟨hτ, fun _ _ ↦ ⊤, fun _ ↦ isPredictableStoppingTime_top F P, ?_⟩
  filter_upwards [h] with ω hω hn
  exact (hn hω).elim

theorem isTotallyInaccessibleStoppingTime_of_ae_eq_top (hτ : IsStoppingTime F τ)
    (h : τ =ᵐ[P] (fun _ ↦ ⊤)) : IsTotallyInaccessibleStoppingTime F τ P := by
  refine ⟨hτ, fun _ _ ↦ ?_⟩
  exact measure_mono_null (fun _ hω ↦ hω.2) (ae_iff.mp h)

theorem isAccessibleStoppingTime_top (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    IsAccessibleStoppingTime F (fun _ ↦ ⊤) P :=
  (isPredictableStoppingTime_top F P).isAccessible

theorem isTotallyInaccessibleStoppingTime_top (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    IsTotallyInaccessibleStoppingTime F (fun _ ↦ ⊤) P :=
  isTotallyInaccessibleStoppingTime_of_ae_eq_top (fun _ ↦ by simp)
    (Eventually.of_forall fun _ ↦ rfl)

theorem IsAccessibleStoppingTime.ae_eq_top_of_totallyInaccessible
    (ha : IsAccessibleStoppingTime F τ P) (ht : IsTotallyInaccessibleStoppingTime F τ P) :
    τ =ᵐ[P] (fun _ ↦ ⊤) := by
  obtain ⟨σ, hσ, hcover⟩ := ha.2
  have hnull (n : ℕ) : ∀ᵐ ω ∂P, ¬ (τ ω = σ n ω ∧ τ ω ≠ ⊤) := by
    rw [ae_iff]
    simpa only [not_not] using ht.2 (σ n) (hσ n)
  filter_upwards [hcover, ae_all_iff.mpr hnull] with ω hω hn
  by_contra hne
  obtain ⟨n, he⟩ := hω hne
  exact hn n ⟨he, hne⟩

/-- The two classes overlap exactly at almost-sure infinity, not at arbitrary
stopping times and not at a non-null finite predictable time. -/
theorem accessible_and_totallyInaccessible_iff_ae_eq_top (hτ : IsStoppingTime F τ) :
    (IsAccessibleStoppingTime F τ P ∧ IsTotallyInaccessibleStoppingTime F τ P) ↔
      τ =ᵐ[P] (fun _ ↦ ⊤) :=
  ⟨fun h ↦ h.1.ae_eq_top_of_totallyInaccessible h.2,
    fun h ↦ ⟨isAccessibleStoppingTime_of_ae_eq_top hτ h,
      isTotallyInaccessibleStoppingTime_of_ae_eq_top hτ h⟩⟩

theorem isAccessibleStoppingTime_of_ae_countable_values (hτ : IsStoppingTime F τ)
    {s : Set (WithTop ℝ≥0)} (hs : s.Countable) (hcover : ∀ᵐ ω ∂P, τ ω ∈ s) :
    IsAccessibleStoppingTime F τ P := by
  obtain ⟨values, hv⟩ := (hs.insert ⊤).exists_eq_range (insert_nonempty ⊤ s)
  refine ⟨hτ, fun n _ ↦ values n, fun n ↦ ?_, ?_⟩
  · change IsPredictableStoppingTime F (fun _ ↦ values n) P
    cases hval : values n with
    | top => exact isPredictableStoppingTime_top F P
    | coe t => exact isPredictableStoppingTime_const F P t
  · filter_upwards [hcover] with ω hω _
    have hm : τ ω ∈ insert ⊤ s := mem_insert_of_mem _ hω
    rw [hv] at hm
    obtain ⟨n, hn⟩ := hm
    exact ⟨n, hn.symm⟩

theorem isAccessibleStoppingTime_of_countable_range (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) : IsAccessibleStoppingTime F τ P :=
  isAccessibleStoppingTime_of_ae_countable_values hτ hcount
    (Eventually.of_forall fun ω ↦ mem_range_self ω)

theorem not_isTotallyInaccessibleStoppingTime_const [IsProbabilityMeasure P] (t : ℝ≥0) :
    ¬ IsTotallyInaccessibleStoppingTime F (fun _ ↦ (t : WithTop ℝ≥0)) P := by
  intro h
  have hz := h.2 (fun _ ↦ (t : WithTop ℝ≥0)) (isPredictableStoppingTime_const F P t)
  have he : {ω : Ω | (t : WithTop ℝ≥0) = t ∧ (t : WithTop ℝ≥0) ≠ ⊤} = univ := by
    ext ω
    exact iff_true_intro ⟨rfl, WithTop.coe_ne_top⟩
  rw [he, measure_univ] at hz
  exact one_ne_zero hz

end ProbabilityTheory
