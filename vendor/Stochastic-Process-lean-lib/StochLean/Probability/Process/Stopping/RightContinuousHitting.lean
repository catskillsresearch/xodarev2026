/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ContinuousHitting
public import StochLean.Probability.Process.Stopping.Usual

/-! # Open-set hitting times for right-continuous processes

The owner is Mathlib's `hittingAfter`. Open hits strictly before a deterministic time
are detected on a fixed countable dense grid. Right continuity of the filtration then
gives the stopping-time property. At a finite hit the path belongs to the closure of
the target, not necessarily the open target itself.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

theorem IsRightContinuousPath.exists_dense_hit_before {x : ℝ≥0 → E}
    (hx : IsRightContinuousPath x) {s : Set E} (hs : IsOpen s)
    {a t T : ℝ≥0} (hat : a ≤ t) (htT : t < T) (hxt : x t ∈ s) :
    ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ico a T ∧ x (denseSeq ℝ≥0 n) ∈ s := by
  have hD : Dense (range (denseSeq ℝ≥0)) := denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hD.exists_seq_strictAnti_tendsto_of_lt htT
  have hwithin : Tendsto u atTop (𝓝[≥] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1.1.le⟩
  have hxu : Tendsto (fun n ↦ x (u n)) atTop (𝓝 (x t)) := (hx t).tendsto.comp hwithin
  have hmem : ∀ᶠ n in atTop, x (u n) ∈ s := hxu (hs.mem_nhds hxt)
  obtain ⟨n, hn⟩ := hmem.exists
  obtain ⟨k, hk⟩ := (hu n).2
  refine ⟨k, ?_⟩
  rw [hk]
  exact ⟨⟨hat.trans (hu n).1.1.le, (hu n).1.2⟩, hn⟩

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

theorem hittingAfter_lt_iff_dense_of_rightContinuous {s : Set E} (hs : IsOpen s)
    {a T : ℝ≥0} {ω : Ω} (hX : ProbabilityTheory.IsRightContinuousPath (X · ω)) :
    hittingAfter X s a ω < T ↔
      ∃ n : ℕ, denseSeq ℝ≥0 n ∈ Ico a T ∧ X (denseSeq ℝ≥0 n) ω ∈ s := by
  rw [hittingAfter_lt_iff]
  constructor
  · rintro ⟨t, ht, hXt⟩
    exact hX.exists_dense_hit_before hs ht.1 ht.2 hXt
  · rintro ⟨n, hn, hXn⟩
    exact ⟨denseSeq ℝ≥0 n, hn, hXn⟩

/-- A finite first hit lies in the closure of its target, by approximation from the right. -/
theorem hittingAfter_mem_closure_of_rightContinuous {s : Set E} {a : ℝ≥0} {ω : Ω}
    (hX : ProbabilityTheory.IsRightContinuousPath (X · ω))
    (hne : hittingAfter X s a ω ≠ ⊤) :
    X (hittingAfter X s a ω).untopA ω ∈ closure s := by
  classical
  have hex : ∃ t, a ≤ t ∧ X t ω ∈ s := by
    simpa only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not, exists_prop] using hne
  let S : Set ℝ≥0 := {t | a ≤ t ∧ X t ω ∈ s}
  have hS : S.Nonempty := hex
  have hbelow : BddBelow S := ⟨0, fun _ _ ↦ bot_le⟩
  obtain ⟨u, _, hlim, hu⟩ := exists_seq_tendsto_sInf hS hbelow
  have hwithin : Tendsto u atTop (𝓝[≥] sInf S) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ csInf_le hbelow (hu n)⟩
  have hxu : Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X (sInf S) ω)) :=
    (hX (sInf S)).tendsto.comp hwithin
  have hmem : X (sInf S) ω ∈ closure s :=
    isClosed_closure.mem_of_tendsto hxu (Eventually.of_forall fun n ↦ subset_closure (hu n).2)
  rw [hittingAfter, if_pos hex]
  exact hmem

theorem hittingAfter_mem_of_rightContinuous {s : Set E} (hs : IsClosed s)
    {a : ℝ≥0} {ω : Ω} (hX : ProbabilityTheory.IsRightContinuousPath (X · ω))
    (hne : hittingAfter X s a ω ≠ ⊤) : X (hittingAfter X s a ω).untopA ω ∈ s := by
  simpa only [hs.closure_eq] using hittingAfter_mem_closure_of_rightContinuous hX hne

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

theorem Adapted.measurableSet_hittingAfter_lt_of_isOpen (hX : Adapted F X)
    (hr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a T : ℝ≥0) :
    MeasurableSet[F T] {ω | hittingAfter X s a ω < T} := by
  have heq : {ω | hittingAfter X s a ω < T} =
      ⋃ n : ℕ, ⋃ (_ : denseSeq ℝ≥0 n ∈ Ico a T), (X (denseSeq ℝ≥0 n)) ⁻¹' s := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage,
      hittingAfter_lt_iff_dense_of_rightContinuous hs (hr ω), exists_prop]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro hn
  exact ((hX _).mono (F.mono hn.2.le) le_rfl) hs.measurableSet

/-- Right-continuous adapted processes hit open sets at stopping times in a
right-continuous filtration. Completeness is not needed on the everywhere-regular domain. -/
theorem Adapted.isStoppingTime_hittingAfter_isOpen [F.IsRightContinuous]
    (hX : Adapted F X) (hr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (X · ω))
    {s : Set E} (hs : IsOpen s) (a : ℝ≥0) : IsStoppingTime F (hittingAfter X s a) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    (hX.measurableSet_hittingAfter_lt_of_isOpen hr hs a)

/-- Usual completeness handles one common exceptional path event; the stopping
time remains the original raw process's hitting time. -/
theorem Adapted.isStoppingTime_hittingAfter_isOpen_of_usual {P : Measure Ω}
    (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : ProbabilityTheory.HasRightContinuousPaths X P)
    {s : Set E} (hs : IsOpen s) (a : ℝ≥0) : IsStoppingTime F (hittingAfter X s a) := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsRightContinuousPath (X · ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hr)
  let Y : ℝ≥0 → Ω → E := fun t ω ↦ if ω ∈ bad then X 0 ω else X t ω
  have hYa : Adapted F Y := fun t ↦ Measurable.ite (F.mono bot_le _ hbad)
    ((hX 0).mono (F.mono bot_le) le_rfl) (hX t)
  have hYr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (Y · ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · intro t
      simp only [Y, if_pos hb]
      exact continuous_const.continuousWithinAt
    · simpa only [Y, if_neg hb] using
        (not_not.mp hb : ProbabilityTheory.IsRightContinuousPath (X · ω))
  let : F.IsRightContinuous := hF.rightContinuous
  apply (hYa.isStoppingTime_hittingAfter_isOpen hYr hs a).congr_ae_of_usual hF
  filter_upwards [hr] with ω hω
  have hb : ω ∉ bad := fun h ↦ h hω
  simp only [hittingAfter, Y, if_neg hb]

end MeasureTheory
