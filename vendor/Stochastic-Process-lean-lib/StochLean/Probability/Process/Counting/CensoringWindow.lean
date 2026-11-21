/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CensoringLaw

/-! # Exact crude-window decomposition under censoring

The observation survival is the joint survival of the arrival and censoring
lifetimes. A crude arrival window conditioned only on survival at its left
endpoint is not the cause-submeasure window: it also contains paths censored
strictly before their arrival inside that window.

The extra triangular event is retained explicitly. The two pieces are
disjoint, with ties assigned to the arrival mark `T ≤ U`. All statements
are extended-measure identities; they need no finite measure, independence,
finite lifetimes, or ordering assumption on the two finite endpoints. No
limiting rate or disappearance of the triangular error is asserted.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*}

private theorem censored_crude_window_event_decomposition
    (T U : Ω → WithTop ℝ≥0) (t u : ℝ≥0) :
    {ω | (t : WithTop ℝ≥0) ≤ T ω ∧ T ω < (u : WithTop ℝ≥0) ∧
        (t : WithTop ℝ≥0) ≤ U ω} =
      {ω | (t : WithTop ℝ≥0) ≤ T ω ∧ T ω < (u : WithTop ℝ≥0) ∧ T ω ≤ U ω} ∪
        {ω | (t : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧ T ω < (u : WithTop ℝ≥0)} ∧
    Disjoint
      {ω | (t : WithTop ℝ≥0) ≤ T ω ∧ T ω < (u : WithTop ℝ≥0) ∧ T ω ≤ U ω}
      {ω | (t : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧ T ω < (u : WithTop ℝ≥0)} := by
  constructor
  · ext ω
    constructor
    · rintro ⟨hTl, hTu, hUl⟩
      by_cases hTU : T ω ≤ U ω
      · exact Or.inl ⟨hTl, hTu, hTU⟩
      · exact Or.inr ⟨hUl, lt_of_not_ge hTU, hTu⟩
    · rintro (⟨hTl, hTu, hTU⟩ | ⟨hUl, hUT, hTu⟩)
      · exact ⟨hTl, hTu, hTl.trans hTU⟩
      · exact ⟨hUl.trans hUT.le, hTu, hUl⟩
  · apply Set.disjoint_left.mpr
    intro ω hA hC
    exact (not_lt_of_ge hA.2.2) hC.2.1

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {T U : Ω → WithTop ℝ≥0}

/-- Observation survival is the actual joint survival of the original
arrival and censoring lifetimes, including equality at the left endpoint. -/
theorem censored_survival_measure_eq (hT : Measurable T) (hU : Measurable U) (t : ℝ≥0) :
    (P.map (fun ω ↦ min (T ω) (U ω))) (Ici (t : WithTop ℝ≥0)) =
      P {ω | (t : WithTop ℝ≥0) ≤ T ω ∧ (t : WithTop ℝ≥0) ≤ U ω} := by
  rw [Measure.map_apply (hT.min hU) measurableSet_Ici]
  congr 1
  ext ω
  change (t : WithTop ℝ≥0) ≤ min (T ω) (U ω) ↔
    (t : WithTop ℝ≥0) ≤ T ω ∧ (t : WithTop ℝ≥0) ≤ U ω
  exact le_min_iff

/-- The original crude window equals the genuine arrival-cause window
plus the disjoint event of censoring strictly before arrival in the window.
The latter error is not removed without a separate limiting argument. -/
theorem censored_crude_window_measure_eq (hT : Measurable T) (hU : Measurable U)
    (t u : ℝ≥0) :
    P {ω | (t : WithTop ℝ≥0) ≤ T ω ∧ T ω < (u : WithTop ℝ≥0) ∧
        (t : WithTop ℝ≥0) ≤ U ω} =
      ((P.restrict {ω | T ω ≤ U ω}).map T)
          (Ico (t : WithTop ℝ≥0) (u : WithTop ℝ≥0)) +
        P {ω | (t : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧ T ω < (u : WithTop ℝ≥0)} := by
  have herror : MeasurableSet
      {ω | (t : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧ T ω < (u : WithTop ℝ≥0)} :=
    (measurableSet_le measurable_const hU).inter
      ((measurableSet_lt hU hT).inter (measurableSet_lt hT measurable_const))
  have hcause : ((P.restrict {ω | T ω ≤ U ω}).map T)
      (Ico (t : WithTop ℝ≥0) (u : WithTop ℝ≥0)) =
      P {ω | (t : WithTop ℝ≥0) ≤ T ω ∧ T ω < (u : WithTop ℝ≥0) ∧ T ω ≤ U ω} := by
    rw [Measure.map_apply hT measurableSet_Ico,
      Measure.restrict_apply (hT measurableSet_Ico)]
    congr 1
    ext ω
    exact and_assoc
  rw [(censored_crude_window_event_decomposition T U t u).1,
    measure_union (censored_crude_window_event_decomposition T U t u).2 herror, hcause]

end ProbabilityTheory
