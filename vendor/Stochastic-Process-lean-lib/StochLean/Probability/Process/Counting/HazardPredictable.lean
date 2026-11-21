/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Hazard
public import StochLean.Probability.Process.Counting.SingleJumpInformation
public import StochLean.Probability.Process.Stopping.PredictableProcess

/-! # Predictability of the actual stopped cumulative hazard

The deterministic real representative of the extended cumulative hazard is
Borel measurable in time. The existing predictable stopping-map theorem
therefore proves predictability of its actual stopping at the lifetime and
at a deterministic finite horizon. This is the original stopped process,
not an indistinguishable replacement or a selected integral version.

The filtration is the raw natural filtration of the full closed Nat-valued
count. No completion, usual conditions, or exclusion of zero and infinite
lifetimes is needed. In particular, a lifetime at the observation endpoint
is retained by the closed count.

This measurability statement holds for every lifetime measure. Interpreting
the real representative as a finite hazard requires the separate finite
measure and positive pre-jump survival hypotheses from `Hazard`: at every
clock bounded by `T`, `0 < μ (Ici T)` gives genuine extended finiteness.
No real integral identity is inferred by totalizing an infinite hazard.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

/-- The actual capped stopped real hazard is strongly predictable in the
original natural filtration of the full closed count. This exact
measurability assertion does not require the separate finite-hazard guard. -/
theorem isStronglyPredictable_capped_stopped_eCumulativeHazard
    (μ : Measure (WithTop ℝ≥0)) (T : ℝ≥0) :
    IsStronglyPredictable
      (Filtration.natural
        (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount measurable_id))
      (fun t v ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id (min t T) v) := by
  classical
  let N : ℝ≥0 → WithTop ℝ≥0 → ℕ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount measurable_id)
  let A : ℝ≥0 → WithTop ℝ≥0 → ℝ := fun r _ ↦ (eCumulativeHazard μ r).toReal
  have hN : StronglyAdapted ℱ N :=
    Filtration.stronglyAdapted_natural (stronglyMeasurable_singleJumpCount measurable_id)
  have hτ : IsStoppingTime ℱ (id : WithTop ℝ≥0 → WithTop ℝ≥0) := by
    intro s
    have he : {v : WithTop ℝ≥0 | id v ≤ (s : WithTop ℝ≥0)} = N s ⁻¹' {1} := by
      ext v
      change v ≤ (s : WithTop ℝ≥0) ↔
        (if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0) = 1
      by_cases hv : v ≤ (s : WithTop ℝ≥0)
      · rw [if_pos hv]
        exact iff_of_true hv rfl
      · rw [if_neg hv]
        exact iff_of_false hv Nat.zero_ne_one
    rw [he]
    exact (hN s).measurable (measurableSet_singleton 1)
  have htime : Measurable[ℱ.predictable]
      (Prod.fst : ℝ≥0 × WithTop ℝ≥0 → ℝ≥0) := by
    apply measurable_of_Ioi
    intro s
    simpa only [prod_univ] using
      measurableSet_predictable_Ioi_prod (𝓕 := ℱ) (i := s) MeasurableSet.univ
  have hA : IsStronglyPredictable ℱ A :=
    ((measurable_eCumulativeHazard μ).ennreal_toReal.comp htime).stronglyMeasurable
  have hp := (hA.stoppedProcess hτ).stoppedProcess (isStoppingTime_const ℱ T)
  have he : stoppedProcess (stoppedProcess A id) (fun _ ↦ (T : WithTop ℝ≥0)) =
      fun t v ↦ stoppedProcess A id (min t T) v := by
    funext t v
    change stoppedProcess A id (min (t : WithTop ℝ≥0) (T : WithTop ℝ≥0)).untopA v = _
    rw [← WithTop.coe_min]
    rfl
  rw [he] at hp
  exact hp

end ProbabilityTheory
