/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingStability

/-! # Comparison with a predictable time before a stopping time

If sigma is predictable and tau is a stopping time, then sigma <= tau is
measurable strictly before tau, provided the initial sigma-field contains
all ambient null sets. A capped announcing sequence gives the comparison
on the positive-tau event. The zero event is handled with initial information,
and completeness turns the almost-sure announcing equivalence into exact
measurability of the original comparison event.

Neither right continuity of the filtration, finiteness of the measure, nor
predictability of the second time is needed. Equality at infinity is allowed
in the equality theorem; the finite-equality theorem removes it explicitly.
These events can later support predictable restrictions and graph deduplication.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {σ τ : Ω → WithTop ℝ≥0}

/-- Comparison with a predictable first time is measurable before the second
stopping time. Initial completeness suffices for the source AE announcing convention. -/
theorem IsPredictableStoppingTime.measurableSet_le_before
    (hσ : IsPredictableStoppingTime F σ P) (hτ : IsStoppingTime F τ)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω ≤ τ ω} := by
  classical
  obtain ⟨η, hη, hηle⟩ := hσ.exists_announcing_le
  have hσ0 : MeasurableSet[F 0] {ω | σ ω = 0} := by
    have he : {ω | σ ω = 0} = {ω | σ ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h bot_le⟩
    rw [he]
    exact hσ.1 0
  have hτ0 : MeasurableSet[hτ.measurableSpaceBefore] {ω | τ ω = 0} :=
    hτ.measurable_before (measurableSet_singleton 0)
  let E : Set Ω := ({ω | τ ω = 0} ∩ {ω | σ ω = 0}) ∪
    ({ω | 0 < τ ω} ∩ ⋂ n : ℕ, {ω | η n ω < τ ω})
  have hE : MeasurableSet[hτ.measurableSpaceBefore] E :=
    (hτ0.inter (hτ.le_measurableSpaceBefore _ hσ0)).union
      ((hτ.measurableSet_gt_before 0).inter
        (MeasurableSet.iInter fun n ↦ (hη.isStoppingTime n).measurableSet_lt_before hτ))
  have he : ∀ᵐ ω ∂P, ω ∈ E ↔ σ ω ≤ τ ω := by
    filter_upwards [hη.tendsto] with ω hω
    simp only [E, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro (⟨hτw, hσw⟩ | ⟨_, hlt⟩)
      · rw [hτw, hσw]
      · exact le_of_tendsto hω (Eventually.of_forall fun n ↦ (hlt n).le)
    · intro hστ
      by_cases hτpos : 0 < τ ω
      · refine Or.inr ⟨hτpos, fun n ↦ ?_⟩
        by_cases hσpos : 0 < σ ω
        · exact (hη.strict n ω hσpos).trans_le hστ
        · have hσw : σ ω = 0 := le_antisymm (le_of_not_gt hσpos) bot_le
          exact (hηle n ω).trans_lt (hσw.le.trans_lt hτpos)
      · have hτw : τ ω = 0 := le_antisymm (le_of_not_gt hτpos) bot_le
        exact Or.inl ⟨hτw, le_antisymm (hστ.trans hτw.le) bot_le⟩
  have hcB : IsCompleteSubMeasurableSpace P hτ.measurableSpaceBefore :=
    fun S hS ↦ hτ.le_measurableSpaceBefore S (hc0 S hS)
  have hχ : E.indicator (fun _ : Ω ↦ (1 : ℝ)) =ᵐ[P]
      {ω | σ ω ≤ τ ω}.indicator (fun _ : Ω ↦ (1 : ℝ)) := by
    filter_upwards [he] with ω hω
    simp only [indicator_apply, mem_ofPred_eq, hω]
  have hm := hcB.measurable_congr_ae (measurable_const.indicator hE) hχ
  convert hm (measurableSet_singleton (1 : ℝ)) using 1
  ext ω
  simp [Set.indicator]

/-- Equality with a predictable time is measurable before the other stopping
time, including equality of two infinite lifetimes. -/
theorem IsPredictableStoppingTime.measurableSet_eq_before
    (hσ : IsPredictableStoppingTime F σ P) (hτ : IsStoppingTime F τ)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω = τ ω} := by
  have he : {ω | σ ω = τ ω} = {ω | σ ω ≤ τ ω} \ {ω | σ ω < τ ω} := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    exact ⟨fun h ↦ ⟨h.le, not_lt_of_ge h.ge⟩,
      fun h ↦ le_antisymm h.1 (le_of_not_gt h.2)⟩
  rw [he]
  exact (hσ.measurableSet_le_before hτ hc0).diff (hσ.1.measurableSet_lt_before hτ)

/-- The finite graph-equality event lies in the native before sigma-field.
Infinity is removed explicitly rather than treated as a finite graph point. -/
theorem IsPredictableStoppingTime.measurableSet_eq_finite_before
    (hσ : IsPredictableStoppingTime F σ P) (hτ : IsStoppingTime F τ)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0)) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | σ ω = τ ω ∧ τ ω ≠ ⊤} := by
  exact (hσ.measurableSet_eq_before hτ hc0).inter
    (hτ.measurable_before (measurableSet_singleton ⊤)).compl

end ProbabilityTheory
