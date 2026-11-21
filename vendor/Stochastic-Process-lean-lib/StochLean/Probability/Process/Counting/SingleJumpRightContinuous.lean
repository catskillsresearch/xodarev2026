/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.SingleJumpInformation

/-! # Right continuity of the raw single-jump natural filtration

An event known immediately after a time has a measurable revealed part at
that time. Its intersection with survival is either empty or the whole
survival event: any two surviving lifetimes still survive at some common
strictly later finite time, where they belong to the same information atom.
The exact closed-count event decomposition therefore proves right continuity.

No measure, null completion, positive lifetime, or finite lifetime is used.
The closed observation endpoint is essential; the raw capped-lifetime field
is not silently substituted for this natural filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {τ : Ω → WithTop ℝ≥0}

/-- The original closed single-jump count has a right-continuous natural
filtration before any completion or usual augmentation. -/
theorem natural_singleJumpCount_isRightContinuous (hτ : Measurable τ) :
    (Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)).IsRightContinuous := by
  classical
  let F := Filtration.natural
    (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount hτ)
  constructor
  intro t E hE
  have hfuture (u : ℝ≥0) (htu : t < u) : MeasurableSet[F u] E := by
    have hle : F.rightCont t ≤ F u := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le u htu
    exact hle E hE
  have ht1 : t < t + 1 := lt_add_of_pos_right t (by norm_num)
  obtain ⟨D, hD, _, hED⟩ :=
    (measurableSet_natural_singleJumpCount_iff hτ (t + 1) E).mp (hfuture (t + 1) ht1)
  let B := D ∩ Iic (t : WithTop ℝ≥0)
  have hB : MeasurableSet B := hD.inter measurableSet_Iic
  have hBt : B ⊆ Iic (t : WithTop ℝ≥0) := inter_subset_right
  have heC : E ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} = τ ⁻¹' B := by
    ext ω
    rcases hED with hED | hED
    · rw [hED]
      rfl
    · rw [hED]
      change ((τ ω ∈ D ∨ ((t + 1 : ℝ≥0) : WithTop ℝ≥0) < τ ω) ∧
        τ ω ≤ (t : WithTop ℝ≥0)) ↔ τ ω ∈ D ∧ τ ω ≤ (t : WithTop ℝ≥0)
      constructor
      · rintro ⟨hω | hs, hc⟩
        · exact ⟨hω, hc⟩
        · exact False.elim ((not_lt_of_ge
            (hc.trans (WithTop.coe_le_coe.mpr ht1.le))) hs)
      · rintro ⟨hω, hc⟩
        exact ⟨Or.inl hω, hc⟩
  apply (measurableSet_natural_singleJumpCount_iff hτ t E).mpr
  refine ⟨B, hB, hBt, ?_⟩
  by_cases hex : ∃ ω, ω ∈ E ∧ (t : WithTop ℝ≥0) < τ ω
  · have hAll : ∀ ω, (t : WithTop ℝ≥0) < τ ω → ω ∈ E := by
      obtain ⟨ω₀, hω₀E, hω₀t⟩ := hex
      intro ω hωt
      obtain ⟨v, htv, hv⟩ := exists_between (lt_min hω₀t hωt)
      cases v with
      | top => exact False.elim ((not_lt_of_ge le_top) hv)
      | coe u =>
        have htu : t < u := WithTop.coe_lt_coe.mp htv
        obtain ⟨C, _, hCu, hEC⟩ :=
          (measurableSet_natural_singleJumpCount_iff hτ u E).mp (hfuture u htu)
        have h₀u : (u : WithTop ℝ≥0) < τ ω₀ := (lt_min_iff.mp hv).1
        have hωu : (u : WithTop ℝ≥0) < τ ω := (lt_min_iff.mp hv).2
        rcases hEC with hEC | hEC
        · have h₀C : τ ω₀ ∈ C := by rwa [hEC] at hω₀E
          exact False.elim ((not_lt_of_ge (hCu h₀C)) h₀u)
        · rw [hEC]
          exact Or.inr hωu
    right
    ext ω
    constructor
    · intro hω
      by_cases hc : τ ω ≤ (t : WithTop ℝ≥0)
      · exact Or.inl ((Set.ext_iff.mp heC ω).mp ⟨hω, hc⟩)
      · exact Or.inr (lt_of_not_ge hc)
    · rintro (hω | hω)
      · exact ((Set.ext_iff.mp heC ω).mpr hω).1
      · exact hAll ω hω
  · left
    ext ω
    constructor
    · intro hω
      have hc : τ ω ≤ (t : WithTop ℝ≥0) := by
        by_contra h
        exact hex ⟨ω, hω, lt_of_not_ge h⟩
      exact (Set.ext_iff.mp heC ω).mp ⟨hω, hc⟩
    · intro hω
      exact ((Set.ext_iff.mp heC ω).mpr hω).1

end ProbabilityTheory
