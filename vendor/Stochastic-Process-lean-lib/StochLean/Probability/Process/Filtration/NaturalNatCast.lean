/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Natural
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.Floor

/-! # The original counting and real-count natural filtrations agree

Casting a natural-valued process to the reals preserves its exact raw
natural filtration. One direction uses the measurable cast; the other
uses the native measurable natural floor, which recovers every original
natural value exactly. Both directions are instances of natural-filtration
minimality, with no measure, completion, path regularity, or version change.
-/

@[expose] public section

namespace MeasureTheory.Filtration

/-- The original natural filtration of a measurable counting process is
exactly the natural filtration of its real cast, for any preordered time
index. The original measurable coordinates supply both natural witnesses. -/
theorem natural_natCast_real_eq
    {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    (N : ι → Ω → ℕ) (hm : ∀ t, Measurable (N t)) :
    Filtration.natural (fun t ω ↦ (N t ω : ℝ))
        (fun t ↦ ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
          (hm t)).stronglyMeasurable) =
      Filtration.natural N (fun t ↦ (hm t).stronglyMeasurable) := by
  have hnat := Filtration.stronglyAdapted_natural (fun t ↦ (hm t).stronglyMeasurable)
  have hreal := Filtration.stronglyAdapted_natural
    (fun t ↦ ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (hm t)).stronglyMeasurable)
  apply le_antisymm
  · apply natural_le_of_stronglyAdapted
    intro t
    exact ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (hnat t).measurable).stronglyMeasurable
  · apply natural_le_of_stronglyAdapted
    intro t
    have hfloor := Nat.measurable_floor.comp (hreal t).measurable
    simpa only [Function.comp_def, Nat.floor_natCast] using hfloor.stronglyMeasurable

end MeasureTheory.Filtration
