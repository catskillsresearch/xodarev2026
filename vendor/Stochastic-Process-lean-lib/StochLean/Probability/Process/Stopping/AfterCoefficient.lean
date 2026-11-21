/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightStep
public import StochLean.Probability.Process.Stopping.OptionalValue

/-! # Revealing stopped information at and after its stopping time

This is the source process used to prove Protter I.6. The coefficient is
measurable at the native stopped field, not prematurely at time zero. Its
activation path is cadlag, including zero and infinite lifetimes.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0} [TopologicalSpace E] [Zero E]

theorem StronglyMeasurable.indicator_stoppingTime_le (hτ : IsStoppingTime F τ)
    {Z : Ω → E} (hZ : StronglyMeasurable[hτ.measurableSpace] Z) (t : ℝ≥0) :
    StronglyMeasurable[F t] ({ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) := by
  have hm := hτ.measurableSet_le' t
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hm ?_
    (hZ.indicator hm) ?_
  · intro A hA
    have hs := hA.2 t
    convert hs using 1
    ext ω
    simp only [mem_inter_iff]
    tauto
  · intro ω hω
    exact Set.indicator_of_notMem hω _

theorem StronglyMeasurable.isStronglyOptional_indicator_stoppingTime_le
    (hτ : IsStoppingTime F τ) {Z : Ω → ℝ} (hZ : StronglyMeasurable[hτ.measurableSpace] Z) :
    IsStronglyOptional F (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) := by
  have ha : Adapted F (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) :=
    fun t ↦ (hZ.indicator_stoppingTime_le hτ t).measurable
  exact ha.isStronglyOptional_of_cadlag (isCadlagPath_indicator_lifetime_le τ Z)

end MeasureTheory
