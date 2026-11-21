/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Announcing

/-! # Stability of announcing sequences

Capping each announcing term by its target preserves the source relation and
makes domination pointwise, even at exceptional zero-time samples. Finite
minima and maxima of predictable times are predictable. No claim about
decreasing limits or arbitrary stopped-event restrictions is made.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ ρ : Ω → WithTop ℝ≥0} {σ π : ℕ → Ω → WithTop ℝ≥0}

theorem IsAnnouncingSequence.cap_target (h : IsAnnouncingSequence F P τ σ)
    (hτ : IsStoppingTime F τ) :
    IsAnnouncingSequence F P τ (fun n ω ↦ min (σ n ω) (τ ω)) := by
  refine ⟨fun n ↦ (h.isStoppingTime n).min hτ,
    fun ω i j hij ↦ min_le_min (h.monotone ω hij) le_rfl,
    fun n ω ht ↦ (min_le_left _ _).trans_lt (h.strict n ω ht), ?_⟩
  filter_upwards [h.tendsto] with ω hω
  simpa only [min_self] using hω.min (tendsto_const_nhds (x := τ ω))

theorem IsPredictableStoppingTime.exists_announcing_le
    (h : IsPredictableStoppingTime F τ P) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, IsAnnouncingSequence F P τ σ ∧ ∀ n ω, σ n ω ≤ τ ω := by
  obtain ⟨σ, hs⟩ := h.2
  exact ⟨fun n ω ↦ min (σ n ω) (τ ω), hs.cap_target h.1, fun _ _ ↦ min_le_right _ _⟩

theorem IsAnnouncingSequence.min (h : IsAnnouncingSequence F P τ σ)
    (h' : IsAnnouncingSequence F P ρ π) :
    IsAnnouncingSequence F P (fun ω ↦ min (τ ω) (ρ ω))
      (fun n ω ↦ min (σ n ω) (π n ω)) := by
  refine ⟨fun n ↦ (h.isStoppingTime n).min (h'.isStoppingTime n),
    fun ω i j hij ↦ min_le_min (h.monotone ω hij) (h'.monotone ω hij),
    fun n ω ht ↦ ?_, ?_⟩
  · exact min_lt_min (h.strict n ω (lt_min_iff.mp ht).1)
      (h'.strict n ω (lt_min_iff.mp ht).2)
  · filter_upwards [h.tendsto, h'.tendsto] with ω hω hω'
    exact hω.min hω'

theorem IsPredictableStoppingTime.min (h : IsPredictableStoppingTime F τ P)
    (h' : IsPredictableStoppingTime F ρ P) :
    IsPredictableStoppingTime F (fun ω ↦ min (τ ω) (ρ ω)) P := by
  obtain ⟨σ, hs⟩ := h.2
  obtain ⟨π, hp⟩ := h'.2
  exact (hs.min hp).predictable (h.1.min h'.1)

theorem IsPredictableStoppingTime.max (h : IsPredictableStoppingTime F τ P)
    (h' : IsPredictableStoppingTime F ρ P) :
    IsPredictableStoppingTime F (fun ω ↦ max (τ ω) (ρ ω)) P := by
  obtain ⟨σ, hs, hsl⟩ := h.exists_announcing_le
  obtain ⟨π, hp, hpl⟩ := h'.exists_announcing_le
  refine ⟨h.1.max h'.1, (fun n ω ↦ Max.max (σ n ω) (π n ω)),
    fun n ↦ (hs.isStoppingTime n).max (hp.isStoppingTime n),
    fun ω i j hij ↦ max_le_max (hs.monotone ω hij) (hp.monotone ω hij),
    fun n ω ht ↦ ?_, ?_⟩
  · apply max_lt_iff.mpr
    constructor
    · by_cases hpos : 0 < τ ω
      · exact (hs.strict n ω hpos).trans_le (le_max_left _ _)
      · have hzero : τ ω = 0 := le_antisymm (le_of_not_gt hpos) bot_le
        exact (hsl n ω).trans_lt (hzero ▸ ht)
    · by_cases hpos : 0 < ρ ω
      · exact (hp.strict n ω hpos).trans_le (le_max_right _ _)
      · have hzero : ρ ω = 0 := le_antisymm (le_of_not_gt hpos) bot_le
        exact (hpl n ω).trans_lt (hzero ▸ ht)
  · filter_upwards [hs.tendsto, hp.tendsto] with ω hω hω'
    exact hω.max hω'

end ProbabilityTheory
