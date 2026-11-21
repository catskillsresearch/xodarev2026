/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.FirstExit
public import StochLean.Probability.Process.Path.Cadlag

/-! # Open-target hitting and exit bounds for left-continuous paths

Dense detection must include the initial time separately: a left-continuous path
on a half-line can have an isolated initial value. At a positive first exit the
norm remains bounded from above, unlike a cadlag first exit with jump overshoot.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

theorem IsLeftContinuousPath.exists_dense_hit_before {x : ℝ≥0 → E}
    (hx : IsLeftContinuousPath x) {s : Set E} (hs : IsOpen s)
    {a t T : ℝ≥0} (hat : a < t) (htT : t < T) (hxt : x t ∈ s) :
    ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ioo a T ∧ x (denseSeq ℝ≥0 n) ∈ s := by
  have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hD.exists_seq_strictMono_tendsto_of_lt hat
  have hwithin : Tendsto u atTop (𝓝[≤] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1.2.le⟩
  have hxu : Tendsto (fun n ↦ x (u n)) atTop (𝓝 (x t)) := (hx t).tendsto.comp hwithin
  have hmem : ∀ᶠ n in atTop, x (u n) ∈ s := hxu (hs.mem_nhds hxt)
  obtain ⟨n, hn⟩ := hmem.exists
  obtain ⟨k, hk⟩ := (hu n).2
  refine ⟨k, ?_⟩
  rw [hk]
  exact ⟨⟨(hu n).1.1, (hu n).1.2.trans htT⟩, hn⟩

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

theorem hittingAfter_lt_iff_dense_of_leftContinuous {s : Set E} (hs : IsOpen s)
    {a T : ℝ≥0} {ω : Ω} (hX : ProbabilityTheory.IsLeftContinuousPath (X · ω)) :
    hittingAfter X s a ω < T ↔ (a < T ∧ X a ω ∈ s) ∨
      ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ioo a T ∧ X (denseSeq ℝ≥0 n) ω ∈ s := by
  rw [hittingAfter_lt_iff]
  constructor
  · rintro ⟨t, ht, hXt⟩
    rcases ht.1.eq_or_lt with hat | hat
    · exact Or.inl ⟨hat.trans_lt ht.2, hat ▸ hXt⟩
    · exact Or.inr (hX.exists_dense_hit_before hs hat ht.2 hXt)
  · rintro (⟨hT, ha⟩ | ⟨n, hn, hXn⟩)
    · exact ⟨a, ⟨le_rfl, hT⟩, ha⟩
    · exact ⟨denseSeq ℝ≥0 n, ⟨hn.1.le, hn.2⟩, hXn⟩

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

theorem Adapted.measurableSet_hittingAfter_lt_of_leftContinuous (hX : Adapted F X)
    (hl : ∀ ω, ProbabilityTheory.IsLeftContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a T : ℝ≥0) :
    MeasurableSet[F T] {ω | hittingAfter X s a ω < T} := by
  have heq : {ω | hittingAfter X s a ω < T} =
      (⋃ (_ : a < T), (X a) ⁻¹' s) ∪
        ⋃ n : ℕ, ⋃ (_ : denseSeq ℝ≥0 n ∈ Ioo a T), (X (denseSeq ℝ≥0 n)) ⁻¹' s := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_preimage,
      hittingAfter_lt_iff_dense_of_leftContinuous hs (hl ω), exists_prop]
  rw [heq]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro ha
    exact ((hX a).mono (F.mono ha.le) le_rfl) hs.measurableSet
  · apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro hn
    exact ((hX _).mono (F.mono hn.2.le) le_rfl) hs.measurableSet

theorem Adapted.isStoppingTime_hittingAfter_isOpen_of_leftContinuous [F.IsRightContinuous]
    (hX : Adapted F X) (hl : ∀ ω, ProbabilityTheory.IsLeftContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a : ℝ≥0) : IsStoppingTime F (hittingAfter X s a) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    (hX.measurableSet_hittingAfter_lt_of_leftContinuous hl hs a)

end MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem norm_le_of_le_hittingAfter_norm_of_pos {a : ℝ} {t : ℝ≥0} {ω : Ω}
    (hl : ProbabilityTheory.IsLeftContinuousPath (X · ω))
    (hpos : (0 : WithTop ℝ≥0) < hittingAfter X {x | a < ‖x‖} 0 ω)
    (ht : (t : WithTop ℝ≥0) ≤ hittingAfter X {x | a < ‖x‖} 0 ω) : ‖X t ω‖ ≤ a := by
  by_cases hlt : (t : WithTop ℝ≥0) < hittingAfter X {x | a < ‖x‖} 0 ω
  · exact norm_le_of_lt_hittingAfter_norm hlt
  · have heq : (t : WithTop ℝ≥0) = hittingAfter X {x | a < ‖x‖} 0 ω :=
      le_antisymm ht (le_of_not_gt hlt)
    have ht0 : (0 : ℝ≥0) < t := WithTop.coe_lt_coe.mp (hpos.trans_eq heq.symm)
    obtain ⟨u, _, hu, hlim⟩ := exists_seq_strictMono_tendsto' ht0
    have hwithin : Tendsto u atTop (𝓝[≤] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hlim, Eventually.of_forall fun n ↦ (hu n).2.le⟩
    apply le_of_tendsto ((hl t).norm.tendsto.comp hwithin)
    exact Eventually.of_forall fun n ↦ norm_le_of_lt_hittingAfter_norm
      ((WithTop.coe_lt_coe.mpr (hu n).2).trans_eq heq)

end MeasureTheory
