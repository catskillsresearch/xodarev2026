/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.SingleJumpInformation

/-! # Information before a marked single jump

The observations are the pair of closed counts for a measurable mark and
its complement. Before the lifetime occurs, their entire observed history
is the constant zero pair. Native natural-filtration events therefore have
either empty or full trace on survival. The original lifetime is a stopping
time because its occurrence is exactly the pair being nonzero.

The mark is only revealed at the jump, not added to initial information.
No measure, positivity or finiteness of the lifetime is assumed. Zero and
infinite lifetimes, and the closed observation endpoint, are retained.
No right continuity or usual augmentation is asserted here.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {τ : Ω → WithTop ℝ≥0} {B : Set Ω}

open Classical in
/-- Each time coordinate of the actual marked pair of counts is strongly
measurable. Neither mark is observed before the common lifetime occurs. -/
theorem stronglyMeasurable_markedSingleJumpCount (hτ : Measurable τ)
    (hB : MeasurableSet B) (t : ℝ≥0) :
    StronglyMeasurable (fun ω ↦
      (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
       if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0)) := by
  have hm₁ : Measurable (fun ω ↦
      if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0) :=
    Measurable.ite ((measurableSet_le hτ measurable_const).inter hB)
      measurable_const measurable_const
  have hm₂ : Measurable (fun ω ↦
      if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0) :=
    Measurable.ite ((measurableSet_le hτ measurable_const).inter hB.compl)
      measurable_const measurable_const
  exact (hm₁.prodMk hm₂).stronglyMeasurable

open Classical in
/-- A genuine natural-filtration event cannot distinguish any two paths
whose marked single jump has not occurred. The survival event is strict. -/
theorem measurableSet_natural_markedSingleJumpCount_on_survival
    (hτ : Measurable τ) (hB : MeasurableSet B) (s : ℝ≥0) {E : Set Ω}
    (hE : MeasurableSet[(Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)) s] E) :
    E ∩ {ω | (s : WithTop ℝ≥0) < τ ω} = ∅ ∨
      E ∩ {ω | (s : WithTop ℝ≥0) < τ ω} = {ω | (s : WithTop ℝ≥0) < τ ω} := by
  let X : ℝ≥0 → Ω → ℕ × ℕ := fun t ω ↦
    (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then 1 else 0,
     if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then 1 else 0)
  change MeasurableSet[(Filtration.natural X
    (stronglyMeasurable_markedSingleJumpCount hτ hB)) s] E at hE
  rw [Filtration.natural_eq_comap] at hE
  obtain ⟨D, _, hDE⟩ := MeasurableSpace.measurableSet_comap.mp hE
  have hzero (ω : Ω) (hω : (s : WithTop ℝ≥0) < τ ω) :
      (fun u : Iic s ↦ X u ω) = fun _ ↦ (0, 0) := by
    funext u
    have hn : ¬ τ ω ≤ ((u : ℝ≥0) : WithTop ℝ≥0) :=
      not_le_of_gt ((WithTop.coe_le_coe.mpr u.property).trans_lt hω)
    simp only [X, hn, false_and, ite_false]
  have hmem (ω : Ω) (hω : (s : WithTop ℝ≥0) < τ ω) :
      ω ∈ E ↔ (fun _ : Iic s ↦ ((0 : ℕ), (0 : ℕ))) ∈ D := by
    rw [← hDE]
    change (fun u : Iic s ↦ X u ω) ∈ D ↔ _
    rw [hzero ω hω]
  by_cases hD : (fun _ : Iic s ↦ ((0 : ℕ), (0 : ℕ))) ∈ D
  · right
    ext ω
    exact ⟨And.right, fun hω ↦ ⟨(hmem ω hω).mpr hD, hω⟩⟩
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hD ((hmem ω hω.2).mp hω.1)

open Classical in
/-- The actual lifetime is a stopping time for the natural filtration of
the marked pair, including a possible initial jump or infinite lifetime. -/
theorem isStoppingTime_natural_markedSingleJumpCount (hτ : Measurable τ)
    (hB : MeasurableSet B) :
    IsStoppingTime (Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)) τ := by
  let X : ℝ≥0 → Ω → ℕ × ℕ := fun t ω ↦
    (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then 1 else 0,
     if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then 1 else 0)
  let F := Filtration.natural X (stronglyMeasurable_markedSingleJumpCount hτ hB)
  intro t
  have hm : Measurable[F t] (X t) :=
    (Filtration.stronglyAdapted_natural
      (stronglyMeasurable_markedSingleJumpCount hτ hB) t).measurable
  have he : {ω | τ ω ≤ (t : WithTop ℝ≥0)} =
      (X t) ⁻¹' ({((0 : ℕ), (0 : ℕ))}ᶜ) := by
    ext ω
    change τ ω ≤ (t : WithTop ℝ≥0) ↔ X t ω ≠ (0, 0)
    constructor
    · intro ht hz
      by_cases hω : ω ∈ B
      · have hf : (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0) = 0 :=
          congrArg Prod.fst hz
        rw [if_pos ⟨ht, hω⟩] at hf
        exact Nat.one_ne_zero hf
      · have hf : (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0) = 0 :=
          congrArg Prod.snd hz
        rw [if_pos ⟨ht, hω⟩] at hf
        exact Nat.one_ne_zero hf
    · intro hn
      by_contra ht
      apply hn
      change (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
        if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0) = (0, 0)
      rw [if_neg (fun h ↦ ht h.1), if_neg (fun h ↦ ht h.1)]
  rw [he]
  exact hm (measurableSet_singleton ((0 : ℕ), (0 : ℕ))).compl

end ProbabilityTheory
