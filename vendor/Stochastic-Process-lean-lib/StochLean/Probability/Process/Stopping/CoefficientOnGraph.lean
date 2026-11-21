/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AfterCoefficient

/-! # Transporting a coefficient on a finite stopping-time collision

Information known at one stopping time is known at a second stopping time on
their finite coincidence event. The target is the native stopped sigma-field,
not the before sigma-field. No predictability, usualness, measure finiteness,
or finite-lifetime assumption is needed; the coefficient is explicitly zero
when the original lifetime is infinite.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {σ Γ : Ω → WithTop ℝ≥0} [TopologicalSpace E] [Zero E]

/-- A stopped-measurable coefficient transfers to the other stopped field on
the finite collision event. This does not assert before-field measurability. -/
theorem StronglyMeasurable.indicator_eq_finite_stoppingTime
    (hσ : IsStoppingTime F σ) (hΓ : IsStoppingTime F Γ) {D : Ω → E}
    (hD : StronglyMeasurable[hσ.measurableSpace] D) :
    StronglyMeasurable[hΓ.measurableSpace]
      ({ω | σ ω = Γ ω ∧ σ ω ≠ ⊤}.indicator D) := by
  let A : Set Ω := {ω | σ ω = Γ ω ∧ σ ω ≠ ⊤}
  have hm : MeasurableSet[hσ.measurableSpace] A :=
    (hσ.measurableSet_eq_stopping_time hΓ).inter
      (hσ.measurable (measurableSet_singleton ⊤)).compl
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hm ?_
    (hD.indicator hm) (fun ω hω ↦ indicator_of_notMem hω D)
  intro S hS
  have ht := (IsStoppingTime.measurableSet_min_iff hσ hΓ _).mp
    (hσ.measurableSet_inter_le hΓ (A ∩ S) hS)
  have he : (A ∩ S) ∩ {ω | σ ω ≤ Γ ω} = A ∩ S := by
    apply inter_eq_left.mpr
    intro ω hω
    exact hω.1.1.le
  simpa only [he] using ht.2

end MeasureTheory
