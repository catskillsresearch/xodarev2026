/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.MarkedSingleJumpInformation

/-! # Right continuity of marked single-jump natural information

An event available immediately after a time has a present-measurable part
on paths whose jump has already occurred: freeze a future observation
history at the present, using that each marked pair remains constant after
its lifetime. On survival, any two paths still survive at some common
strictly later time. The existing trivial-trace theorem then shows that
they cannot be distinguished by the event.

This proves right continuity of the original natural filtration without a
measure or completion. Zero and infinite lifetimes remain permitted, and
the mark is not added to initial information before the jump.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {τ : Ω → WithTop ℝ≥0} {B : Set Ω}

open Classical in
/-- The actual marked pair of closed counts generates a right-continuous
raw natural filtration, with no measure or lifetime-finiteness assumption. -/
theorem natural_markedSingleJumpCount_isRightContinuous
    (hτ : Measurable τ) (hB : MeasurableSet B) :
    (Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)).IsRightContinuous := by
  let X : ℝ≥0 → Ω → ℕ × ℕ := fun t ω ↦
    (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then 1 else 0,
     if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then 1 else 0)
  let hX : ∀ t, StronglyMeasurable (X t) :=
    stronglyMeasurable_markedSingleJumpCount hτ hB
  let F := Filtration.natural X hX
  have ha : StronglyAdapted F X := Filtration.stronglyAdapted_natural hX
  have hstop : IsStoppingTime F τ := isStoppingTime_natural_markedSingleJumpCount hτ hB
  constructor
  intro t E hE
  have hfuture (u : ℝ≥0) (htu : t < u) : MeasurableSet[F u] E := by
    have hle : F.rightCont t ≤ F u := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le u htu
    exact hle E hE
  have hEt1 := hfuture (t + 1) (lt_add_one t)
  change MeasurableSet[(Filtration.natural X hX) (t + 1)] E at hEt1
  rw [Filtration.natural_eq_comap] at hEt1
  obtain ⟨D, hD, hDE⟩ := MeasurableSpace.measurableSet_comap.mp hEt1
  let C : Set Ω := (fun ω (u : Iic (t + 1)) ↦ X (min u t) ω) ⁻¹' D
  have hC : MeasurableSet[F t] C := by
    have hm : Measurable[F t] (fun ω (u : Iic (t + 1)) ↦ X (min u t) ω) := by
      let : MeasurableSpace Ω := F t
      exact measurable_pi_lambda _ fun u ↦
        (ha.stronglyMeasurable_le (min_le_right (u : ℝ≥0) t)).measurable
    exact hm hD
  have hfrozen (ω : Ω) (hω : τ ω ≤ (t : WithTop ℝ≥0)) :
      (fun u : Iic (t + 1) ↦ X (min u t) ω) = fun u : Iic (t + 1) ↦ X u ω := by
    funext u
    by_cases hut : (u : ℝ≥0) ≤ t
    · rw [min_eq_left hut]
    · have htu : t ≤ (u : ℝ≥0) := le_of_not_ge hut
      rw [min_eq_right htu]
      have hωu : τ ω ≤ ((u : ℝ≥0) : WithTop ℝ≥0) :=
        hω.trans (WithTop.coe_le_coe.mpr htu)
      simp only [X, hω, hωu, true_and]
  have hmem (ω : Ω) (hω : τ ω ≤ (t : WithTop ℝ≥0)) : ω ∈ C ↔ ω ∈ E := by
    change (fun u : Iic (t + 1) ↦ X (min u t) ω) ∈ D ↔ ω ∈ E
    rw [hfrozen ω hω]
    exact Set.ext_iff.mp hDE ω
  have hpart : MeasurableSet[F t] (E ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) := by
    have he : E ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} =
        C ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      exact ⟨fun h ↦ ⟨(hmem ω h.2).mpr h.1, h.2⟩,
        fun h ↦ ⟨(hmem ω h.2).mp h.1, h.2⟩⟩
    rw [he]
    exact hC.inter (hstop t)
  have hsurv : MeasurableSet[F t] {ω | (t : WithTop ℝ≥0) < τ ω} := by
    simpa only [compl_ofPred, not_le] using (hstop t).compl
  by_cases hex : ∃ ω, ω ∈ E ∧ (t : WithTop ℝ≥0) < τ ω
  · have hall : ∀ ω, (t : WithTop ℝ≥0) < τ ω → ω ∈ E := by
      obtain ⟨ω₀, h₀E, h₀t⟩ := hex
      intro ω hωt
      obtain ⟨v, htv, hv⟩ := exists_between (lt_min h₀t hωt)
      cases v with
      | top => exact False.elim ((not_lt_of_ge le_top) hv)
      | coe u =>
          have htu : t < u := WithTop.coe_lt_coe.mp htv
          have h₀u : (u : WithTop ℝ≥0) < τ ω₀ := (lt_min_iff.mp hv).1
          have hωu : (u : WithTop ℝ≥0) < τ ω := (lt_min_iff.mp hv).2
          rcases measurableSet_natural_markedSingleJumpCount_on_survival
              hτ hB u (hfuture u htu) with hz | ha
          · have hh : ω₀ ∈ (∅ : Set Ω) := hz ▸ (show ω₀ ∈
                E ∩ {w | (u : WithTop ℝ≥0) < τ w} from ⟨h₀E, h₀u⟩)
            exact False.elim (notMem_empty ω₀ hh)
          · exact ((Set.ext_iff.mp ha ω).mpr hωu).1
    have he : E = (E ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) ∪
        {ω | (t : WithTop ℝ≥0) < τ ω} := by
      ext ω
      constructor
      · intro hω
        by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
        · exact Or.inl ⟨hω, ht⟩
        · exact Or.inr (lt_of_not_ge ht)
      · rintro (hω | hω)
        · exact hω.1
        · exact hall ω hω
    rw [he]
    exact hpart.union hsurv
  · have he : E = E ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      constructor
      · intro hω
        refine ⟨hω, ?_⟩
        by_contra ht
        exact hex ⟨ω, hω, lt_of_not_ge ht⟩
      · exact And.left
    rw [he]
    exact hpart

end ProbabilityTheory
