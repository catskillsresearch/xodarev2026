/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingExamples

/-! # Deterministic delays of nonnegative stopping times

Native stopping-time addition currently covers additive groups or countable
time domains. This nonnegative-real bridge uses truncated subtraction and
handles infinity explicitly. No right continuity of the filtration is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem add_const_nnreal (hτ : IsStoppingTime F τ) (c : ℝ≥0) :
    IsStoppingTime F (fun ω ↦ τ ω + (c : WithTop ℝ≥0)) := by
  intro t
  by_cases hct : c ≤ t
  · have he : {ω | τ ω + (c : WithTop ℝ≥0) ≤ t} = {ω | τ ω ≤ (t - c : ℝ≥0)} := by
      ext ω
      change τ ω + (c : WithTop ℝ≥0) ≤ t ↔ τ ω ≤ (t - c : ℝ≥0)
      cases τ ω with
      | top =>
        rw [WithTop.top_add]
        exact iff_of_false (WithTop.not_top_le_coe t) (WithTop.not_top_le_coe (t - c))
      | coe s =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
        exact (le_tsub_iff_right hct).symm
    rw [he]
    exact F.mono tsub_le_self _ (hτ (t - c))
  · have he : {ω | τ ω + (c : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      change τ ω + (c : WithTop ℝ≥0) ≤ t ↔ False
      cases τ ω with
      | top =>
        rw [WithTop.top_add]
        exact iff_false_intro (WithTop.not_top_le_coe t)
      | coe s =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        exact iff_false_intro (fun h ↦ hct
          ((le_add_of_nonneg_left (show 0 ≤ s from zero_le)).trans h))
    rw [he]
    exact @MeasurableSet.empty Ω (F t)

end MeasureTheory.IsStoppingTime
