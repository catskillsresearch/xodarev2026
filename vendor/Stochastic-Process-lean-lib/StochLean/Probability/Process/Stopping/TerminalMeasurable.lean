/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.TerminalValue
public import StochLean.Probability.Process.Filtration.Terminal

/-! # Native stopping measurability of terminal-valued evaluation

A terminal-filtration-measurable input becomes measurable at the stopping
time after restriction to its infinite-time event. Ambient measurability alone
is not substituted for this terminal condition.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {Y : Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem StronglyMeasurable.indicator_stoppingTime_eq_top
    (hY : StronglyMeasurable[⨆ t, F t] Y) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace] ({ω | τ ω = ⊤}.indicator Y) := by
  have hA := hτ.measurableSet_eq_top'
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hA ?_
    (hY.indicator hA) ?_
  · intro B hB
    refine ⟨hB, fun t ↦ ?_⟩
    have he : ({ω | τ ω = ⊤} ∩ B) ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ht, _⟩, hle⟩
      rw [ht] at hle
      exact WithTop.not_top_le_coe t hle
    rw [he]
    exact @MeasurableSet.empty Ω (F t)
  · intro ω hω
    exact Set.indicator_of_notMem hω _

theorem IsStronglyProgressive.stronglyMeasurable_stoppedValueWithTerminal
    (hX : IsStronglyProgressive F X) (hY : StronglyMeasurable[⨆ t, F t] Y)
    (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValueWithTerminal X Y τ) := by
  classical
  have hA : MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} :=
    (measurableSet_singleton _).preimage hτ.measurable
  have h := (hY.indicator_stoppingTime_eq_top hτ).add
    ((measurable_stoppedValue hX hτ).stronglyMeasurable.indicator hA.compl)
  have he : stoppedValueWithTerminal X Y τ =
      {ω | τ ω = ⊤}.indicator Y + {ω | τ ω = ⊤}ᶜ.indicator (stoppedValue X τ) := by
    funext ω
    by_cases ht : τ ω = ⊤ <;> simp [stoppedValueWithTerminal, Set.indicator, ht]
  rwa [he]

end MeasureTheory
