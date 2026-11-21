/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.BeforeSigma

/-! # Strict comparison events in the pre-stopping sigma-field

Protter III.7 uses a countable union over deterministic times strictly between
the two stopping times. Infinite upper times are allowed. Terminal information
is also measurable before `T` after restriction to `{T = ∞}`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {σ τ : Ω → WithTop ℝ≥0}

private theorem exists_rat_between_withTop {a b : WithTop ℝ≥0} (hab : a < b) :
    ∃ q : ℚ, a < (Real.toNNReal q : WithTop ℝ≥0) ∧
      (Real.toNNReal q : WithTop ℝ≥0) < b := by
  cases a with
  | top => exact False.elim (not_lt_of_ge le_top hab)
  | coe a =>
    cases b with
    | top =>
      obtain ⟨q, _, haq, _⟩ := (NNReal.lt_iff_exists_rat_btwn a (a + 1)).mp
        (lt_add_one a)
      exact ⟨q, WithTop.coe_lt_coe.mpr haq, WithTop.coe_lt_top _⟩
    | coe b =>
      obtain ⟨q, _, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).mp
        (WithTop.coe_lt_coe.mp hab)
      exact ⟨q, WithTop.coe_lt_coe.mpr haq, WithTop.coe_lt_coe.mpr hqb⟩

/-- Protter III.7, with both stopping times allowed to take the value infinity. -/
theorem measurableSet_inter_lt_before (hσ : IsStoppingTime F σ)
    (hτ : IsStoppingTime F τ) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    MeasurableSet[hτ.measurableSpaceBefore] (A ∩ {ω | σ ω < τ ω}) := by
  have he : A ∩ {ω | σ ω < τ ω} = ⋃ q : ℚ,
      (A ∩ {ω | σ ω ≤ (Real.toNNReal q : WithTop ℝ≥0)}) ∩
        {ω | (Real.toNNReal q : WithTop ℝ≥0) < τ ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hω, hlt⟩
      obtain ⟨q, hq, hq'⟩ := exists_rat_between_withTop hlt
      exact ⟨q, ⟨hω, hq.le⟩, hq'⟩
    · rintro ⟨q, ⟨hω, hq⟩, hq'⟩
      exact ⟨hω, hq.trans_lt hq'⟩
  rw [he]
  exact MeasurableSet.iUnion fun q ↦ hτ.measurableSet_inter_gt_before _ (hA.2 _)

theorem measurableSet_lt_before (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω < τ ω} := by
  simpa only [univ_inter] using hσ.measurableSet_inter_lt_before hτ MeasurableSet.univ

theorem measurableSpaceBefore_mono (hσ : IsStoppingTime F σ)
    (hτ : IsStoppingTime F τ) (hστ : σ ≤ τ) :
    hσ.measurableSpaceBefore ≤ hτ.measurableSpaceBefore := by
  refine sup_le hτ.le_measurableSpaceBefore (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨t, A, hA, rfl⟩
  have he : A ∩ {ω | (t : WithTop ℝ≥0) < σ ω} =
      (A ∩ {ω | (t : WithTop ℝ≥0) < σ ω}) ∩ {ω | (t : WithTop ℝ≥0) < τ ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, iff_self_and]
    exact fun hω ↦ hω.2.trans_le (hστ ω)
  rw [he]
  exact hτ.measurableSet_inter_gt_before t (hA.inter (hσ.measurableSet_gt t))

/-- Terminal information restricted to the infinite-lifetime event is already
in the sigma-field strictly before that lifetime. -/
theorem measurableSet_inter_eq_top_before (hτ : IsStoppingTime F τ) {A : Set Ω}
    (hA : MeasurableSet[⨆ t, F t] A) :
    MeasurableSet[hτ.measurableSpaceBefore] (A ∩ {ω | τ ω = ⊤}) := by
  have htop : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω = ⊤} :=
    hτ.measurable_before (measurableSet_singleton _)
  let C : MeasurableSpace Ω := MeasurableSpace.comap Subtype.val
    hτ.measurableSpaceBefore |>.map (fun ω : {ω : Ω | τ ω = ⊤} ↦ (ω : Ω))
  have hle : (⨆ t, F t) ≤ C := by
    refine iSup_le fun t A hA ↦ ?_
    change MeasurableSet[MeasurableSpace.comap Subtype.val hτ.measurableSpaceBefore]
      ((fun ω : {ω : Ω | τ ω = ⊤} ↦ (ω : Ω)) ⁻¹' A)
    have hm := hτ.measurableSet_inter_gt_before t hA
    have he : (fun ω : {ω : Ω | τ ω = ⊤} ↦ (ω : Ω)) ⁻¹' A =
        (fun ω : {ω : Ω | τ ω = ⊤} ↦ (ω : Ω)) ⁻¹'
          (A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}) := by
      ext ω
      change (ω : Ω) ∈ A ↔ (ω : Ω) ∈ A ∧ (t : WithTop ℝ≥0) < τ ω
      rw [show τ ω = ⊤ from ω.2]
      simp only [WithTop.coe_lt_top, and_true]
    rw [he]
    exact ⟨_, hm, rfl⟩
  have hm := hle A hA
  change MeasurableSet[MeasurableSpace.comap Subtype.val hτ.measurableSpaceBefore]
    ((fun ω : {ω : Ω | τ ω = ⊤} ↦ (ω : Ω)) ⁻¹' A) at hm
  rcases hm with ⟨B, hB, hBA⟩
  have he : A ∩ {ω | τ ω = ⊤} = B ∩ {ω | τ ω = ⊤} := by
    ext ω
    by_cases ht : τ ω = ⊤
    · have hx := Set.ext_iff.mp hBA ⟨ω, ht⟩
      change (ω ∈ B ↔ ω ∈ A) at hx
      simpa only [mem_inter_iff, mem_ofPred_eq, ht, and_true] using hx.symm
    · simp only [mem_inter_iff, mem_ofPred_eq, ht, and_false]
  rw [he]
  exact hB.inter htop

end MeasureTheory.IsStoppingTime
