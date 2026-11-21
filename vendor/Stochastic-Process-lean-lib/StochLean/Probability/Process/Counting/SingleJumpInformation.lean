/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Natural
public import StochLean.Probability.Process.Stopping.Restriction
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! # The exact information of a closed single-jump count

The natural filtration of the original count `1_{τ ≤ t}` records the
lifetime itself when it has occurred, and otherwise records infinity.
This is the existing `restrictedStoppingTime`, not a new lifetime selector.

At a possible atom `τ = t`, the raw variable `min τ t` does not generate
this information: it identifies `τ = t` with `τ > t`, whereas the closed
count distinguishes them. This corrects the raw-information identification
used in the discussion preceding Protter III.21. No completion or
right-continuous augmentation is asserted here.

All equalities are exact, including zero, the observation endpoint, and
an infinite lifetime. No probability measure or positivity assumption is
needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {τ : Ω → WithTop ℝ≥0}

/-- Every coordinate of the original closed Nat-valued single-jump count
is strongly measurable when the extended lifetime is measurable. -/
theorem stronglyMeasurable_singleJumpCount (hτ : Measurable τ) (s : ℝ≥0) :
    StronglyMeasurable
      (fun ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0) := by
  exact (Measurable.ite (measurableSet_le hτ measurable_const)
    measurable_const measurable_const).stronglyMeasurable

private theorem restricted_le_observation_iff (t s : ℝ≥0) (ω : Ω) :
    restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)} ω ≤
        (s : WithTop ℝ≥0) ↔
      τ ω ≤ (s : WithTop ℝ≥0) ∧ τ ω ≤ (t : WithTop ℝ≥0) := by
  classical
  by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
  · rw [restrictedStoppingTime_of_mem τ h]
    exact ⟨fun hs ↦ ⟨hs, h⟩, And.left⟩
  · rw [restrictedStoppingTime_of_notMem τ h]
    simp only [WithTop.not_top_le_coe, false_iff]
    exact fun hs ↦ h hs.2

/-- The natural information of all the closed counts up to `t` is exactly
the information of the lifetime restricted to its occurrence by `t`. -/
theorem natural_singleJumpCount_eq_comap_restricted (hτ : Measurable τ)
    (t : ℝ≥0) :
    (Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)) t =
      MeasurableSpace.comap
        (restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) inferInstance := by
  classical
  let N : ℝ≥0 → Ω → ℕ :=
    fun s ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount hτ)
  let R := restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)}
  let mR := MeasurableSpace.comap R inferInstance
  have hR : Measurable[mR] R := measurable_iff_comap_le.mpr le_rfl
  apply le_antisymm
  · change (⨆ s ≤ t, MeasurableSpace.comap (N s) inferInstance) ≤ mR
    apply iSup₂_le
    intro s hst
    have he : {ω | τ ω ≤ (s : WithTop ℝ≥0)} =
        {ω | R ω ≤ (s : WithTop ℝ≥0)} := by
      ext ω
      change τ ω ≤ (s : WithTop ℝ≥0) ↔ R ω ≤ (s : WithTop ℝ≥0)
      rw [restricted_le_observation_iff]
      exact ⟨fun h ↦ ⟨h, h.trans (WithTop.coe_le_coe.mpr hst)⟩, And.left⟩
    have hs : MeasurableSet[mR] {ω | τ ω ≤ (s : WithTop ℝ≥0)} := by
      rw [he]
      exact measurableSet_le hR measurable_const
    exact (Measurable.ite hs measurable_const measurable_const).comap_le
  · change mR ≤ ℱ t
    apply Measurable.comap_le
    apply measurable_of_Iic
    intro v
    cases v with
    | top => simp
    | coe s =>
      have hN : StronglyAdapted ℱ N :=
        Filtration.stronglyAdapted_natural (stronglyMeasurable_singleJumpCount hτ)
      have hm : Measurable[ℱ t] (N (min s t)) :=
        (hN.stronglyMeasurable_le (min_le_right s t)).measurable
      have he : R ⁻¹' Iic (s : WithTop ℝ≥0) = N (min s t) ⁻¹' {1} := by
        ext ω
        change R ω ≤ (s : WithTop ℝ≥0) ↔ N (min s t) ω = 1
        rw [restricted_le_observation_iff]
        have hmin : τ ω ≤ ((min s t : ℝ≥0) : WithTop ℝ≥0) ↔
            τ ω ≤ (s : WithTop ℝ≥0) ∧ τ ω ≤ (t : WithTop ℝ≥0) := by
          change τ ω ≤ min (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔ _
          exact le_min_iff
        change _ ↔ (if τ ω ≤ ((min s t : ℝ≥0) : WithTop ℝ≥0) then 1 else 0) = 1
        by_cases h : τ ω ≤ ((min s t : ℝ≥0) : WithTop ℝ≥0)
        · rw [if_pos h]
          exact iff_of_true (hmin.mp h) rfl
        · rw [if_neg h]
          exact iff_of_false (fun hs ↦ h (hmin.mpr hs)) (by decide)
      rw [he]
      exact hm (measurableSet_singleton 1)

/-- A raw natural-information event is a measurable lifetime event before
the observation endpoint, optionally united with the entire survival event.
The survival event is `t < τ`, not `t ≤ τ`. -/
theorem measurableSet_natural_singleJumpCount_iff (hτ : Measurable τ)
    (t : ℝ≥0) (E : Set Ω) :
    MeasurableSet[(Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)) t] E ↔
      ∃ B : Set (WithTop ℝ≥0), MeasurableSet B ∧
        B ⊆ Iic (t : WithTop ℝ≥0) ∧
        (E = τ ⁻¹' B ∨ E = τ ⁻¹' B ∪ {ω | (t : WithTop ℝ≥0) < τ ω}) := by
  classical
  rw [natural_singleJumpCount_eq_comap_restricted hτ t]
  constructor
  · intro hE
    obtain ⟨D, hD, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hE
    refine ⟨D ∩ Iic (t : WithTop ℝ≥0), hD.inter measurableSet_Iic,
      inter_subset_right, ?_⟩
    by_cases hd : (⊤ : WithTop ℝ≥0) ∈ D
    · right
      ext ω
      simp only [mem_preimage, mem_union, mem_inter_iff, mem_Iic, mem_ofPred_eq]
      by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
      · rw [restrictedStoppingTime_of_mem τ h]
        exact ⟨fun hD ↦ Or.inl ⟨hD, h⟩,
          fun hD ↦ hD.elim And.left (fun ht ↦ (not_lt_of_ge h ht).elim)⟩
      · rw [restrictedStoppingTime_of_notMem τ h]
        exact ⟨fun _ ↦ Or.inr (lt_of_not_ge h), fun _ ↦ hd⟩
    · left
      ext ω
      simp only [mem_preimage, mem_inter_iff, mem_Iic]
      by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
      · rw [restrictedStoppingTime_of_mem τ h]
        exact ⟨fun hD ↦ ⟨hD, h⟩, And.left⟩
      · rw [restrictedStoppingTime_of_notMem τ h]
        exact ⟨fun hD ↦ (hd hD).elim, fun hD ↦ (h hD.2).elim⟩
  · rintro ⟨B, hB, hBt, he⟩
    have htop : (⊤ : WithTop ℝ≥0) ∉ B := by
      intro h
      exact WithTop.not_top_le_coe t (hBt h)
    have hpre :
        (restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) ⁻¹' B =
          τ ⁻¹' B := by
      ext ω
      simp only [mem_preimage]
      by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
      · rw [restrictedStoppingTime_of_mem τ h]
      · have hb : τ ω ∉ B := fun hb ↦ h (hBt hb)
        rw [restrictedStoppingTime_of_notMem τ h]
        exact iff_of_false htop hb
    have hm : MeasurableSet[MeasurableSpace.comap
        (restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) inferInstance]
        (τ ⁻¹' B) := ⟨B, hB, hpre⟩
    have hs : MeasurableSet[MeasurableSpace.comap
        (restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) inferInstance]
        {ω | (t : WithTop ℝ≥0) < τ ω} := by
      refine ⟨{⊤}, measurableSet_singleton ⊤, ?_⟩
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
      · have hn : τ ω ≠ ⊤ := by
          intro hn
          exact WithTop.not_top_le_coe t (hn ▸ h)
        rw [restrictedStoppingTime_of_mem τ h]
        exact iff_of_false hn (not_lt_of_ge h)
      · rw [restrictedStoppingTime_of_notMem τ h]
        exact iff_of_true rfl (lt_of_not_ge h)
    rcases he with rfl | rfl
    · exact hm
    · exact hm.union hs

end ProbabilityTheory
