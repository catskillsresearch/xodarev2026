/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict

/-! # The observed-arrival submeasure under censoring

For an arrival lifetime `T` and censoring lifetime `U`, the observation is
their minimum, with arrival mark `T ≤ U`. Ties belong to the arrival mark,
including a possible tie at infinity. On that mark the observation is
exactly `T`, so its restricted pushforward is a submeasure both of the
observation law and of the original arrival law.

These are actual restricted measures, not normalized conditional laws.
Neither independence nor finite lifetimes nor finiteness of the underlying
measure is required. No lifetime, hazard or compensator selector is added.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*}

/-- At every finite horizon, an observation marked as an arrival has
occurred exactly when the original arrival has occurred. Ties are retained. -/
theorem censored_arrival_event_eq (T U : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    {ω | min (T ω) (U ω) ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω} =
      {ω | T ω ≤ (t : WithTop ℝ≥0) ∧ T ω ≤ U ω} := by
  ext ω
  constructor
  · rintro ⟨ht, hmark⟩
    exact ⟨(min_eq_left hmark) ▸ ht, hmark⟩
  · rintro ⟨ht, hmark⟩
    exact ⟨(min_eq_left hmark).symm ▸ ht, hmark⟩

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {T U : Ω → WithTop ℝ≥0}

/-- The arrival-marked observation law is the corresponding restricted
arrival law, dominated by both original marginal laws. It is not normalized. -/
theorem censored_arrival_submeasure_eq_and_le (hT : Measurable T) (hU : Measurable U) :
    let X : Ω → WithTop ℝ≥0 := fun ω ↦ min (T ω) (U ω)
    let μ := P.map X
    let ρ := (P.restrict {ω | T ω ≤ U ω}).map X
    ρ = (P.restrict {ω | T ω ≤ U ω}).map T ∧ ρ ≤ μ ∧ ρ ≤ P.map T := by
  intro X μ ρ
  have hmark : MeasurableSet {ω | T ω ≤ U ω} := measurableSet_le hT hU
  have he : ρ = (P.restrict {ω | T ω ≤ U ω}).map T := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hmark] with ω hω
    exact min_eq_left hω
  refine ⟨he, Measure.map_mono Measure.restrict_le_self (hT.min hU), ?_⟩
  rw [he]
  exact Measure.map_mono Measure.restrict_le_self hT

end ProbabilityTheory
