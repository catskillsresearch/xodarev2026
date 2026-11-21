/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Announcing

/-! # The sigma-field of an announcing sequence

Protter III.6 uses only initial completeness, not right continuity of the
filtration. Both inclusions handle the source almost-sure convergence using
that completeness. The zero-lifetime event is retained explicitly.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsAnnouncingSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {P : Measure Ω} {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

private theorem measurableSet_congr_of_complete {m : MeasurableSpace Ω}
    (hc : IsCompleteSubMeasurableSpace P m) {A B : Set Ω} (hA : MeasurableSet[m] A)
    (he : ∀ᵐ ω ∂P, ω ∈ A ↔ ω ∈ B) : MeasurableSet[m] B := by
  let N := {ω | ¬ (ω ∈ A ↔ ω ∈ B)}
  have hn : P N = 0 := ae_iff.mp he
  have heq : B = (A \ N) ∪ (B ∩ N) := by
    ext ω
    by_cases hω : ω ∈ A ↔ ω ∈ B <;> simp [N, hω]
  rw [heq]
  exact (hA.diff (hc N hn)).union (hc.mono_null hn inter_subset_right)

/-- Protter III.6 with the actual almost-sure announcing convention, including
zero and infinity. Initial completeness suffices; right continuity is unnecessary. -/
theorem measurableSpaceBefore_eq_iSup (h : IsAnnouncingSequence F P τ σ)
    (hτ : IsStoppingTime F τ) (hc : IsCompleteSubMeasurableSpace P (F 0)) :
    hτ.measurableSpaceBefore = ⨆ n, (h.isStoppingTime n).measurableSpace := by
  have hcB : IsCompleteSubMeasurableSpace P hτ.measurableSpaceBefore :=
    fun A hA ↦ hτ.le_measurableSpaceBefore A (hc A hA)
  have h0 : F 0 ≤ ⨆ n, (h.isStoppingTime n).measurableSpace :=
    ((h.isStoppingTime 0).le_measurableSpace_of_const_le fun _ ↦ bot_le).trans
      (le_iSup (fun n ↦ (h.isStoppingTime n).measurableSpace) 0)
  have hcS : IsCompleteSubMeasurableSpace P (⨆ n, (h.isStoppingTime n).measurableSpace) :=
    fun A hA ↦ h0 A (hc A hA)
  apply le_antisymm
  · refine sup_le h0 (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨t, A, hA, rfl⟩
    have hm : MeasurableSet[⨆ n, (h.isStoppingTime n).measurableSpace]
        (⋃ n, A ∩ {ω | (t : WithTop ℝ≥0) < σ n ω}) :=
      MeasurableSet.iUnion fun n ↦ le_iSup (fun n ↦ (h.isStoppingTime n).measurableSpace) n _
        ((h.isStoppingTime n).measurableSpaceBefore_le _
          ((h.isStoppingTime n).measurableSet_inter_gt_before t hA))
    apply measurableSet_congr_of_complete hcS hm
    filter_upwards [h.tendsto] with ω hω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hAω, hn⟩
      exact ⟨hAω, hn.trans_le ((h.monotone ω).ge_of_tendsto hω n)⟩
    · rintro ⟨hAω, ht⟩
      obtain ⟨n, hn⟩ := (hω.eventually (Ioi_mem_nhds ht)).exists
      exact ⟨n, hAω, hn⟩
  · refine iSup_le fun n A hA ↦ ?_
    have hlt := (h.isStoppingTime n).measurableSet_inter_lt_before hτ hA
    have hz := hτ.le_measurableSpaceBefore _ (hA.2 0)
    apply measurableSet_congr_of_complete hcB (hlt.union hz)
    filter_upwards [h.ae_eq_zero_of_zero] with ω hω
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · exact fun hω ↦ hω.elim And.left And.left
    · intro hAω
      by_cases ht : 0 < τ ω
      · exact Or.inl ⟨hAω, h.strict n ω ht⟩
      · have he : τ ω = 0 := le_antisymm (le_of_not_gt ht) bot_le
        exact Or.inr ⟨hAω, (hω he n).le⟩

end ProbabilityTheory.IsAnnouncingSequence
