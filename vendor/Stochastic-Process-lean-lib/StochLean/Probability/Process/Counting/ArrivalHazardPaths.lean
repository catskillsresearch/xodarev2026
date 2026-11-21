/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalStoppingInformation
public import StochLean.Probability.Process.Counting.ConditionalHazardPathClock
public import StochLean.Probability.Process.Counting.ArrivalGapClock
public import StochLean.Probability.Process.Counting.DelayedHazardSupport

/-! # Path properties of the actual conditional arrival hazards

The history for stage `n` consists of the first `n` original arrival times.
It is available at the previous arrival, not at the initial time. The native
conditional law of the actual absorbing gap therefore gives a predictable
delayed hazard in the actual count's raw natural filtration.

Its zero initial value is pointwise, including the stage-zero birth endpoint.
Its monotone and cadlag path properties hold together on one full-measure
event, transferred through the exact safe-clock identity for the original
stopped delayed hazard. Neither path properties nor a candidate hazard are
assumed, and no new history, clock, conditional distribution or process owner
is introduced. No standard Borel assumption is imposed on the sample space.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- Each original conditional arrival hazard is predictable in the raw
natural count filtration, starts exactly at zero, and has monotone cadlag
paths on one common event. The two path projections are the native
`HasMonotonePaths` and `HasCadlagPaths` properties. -/
theorem predictable_zero_monotone_cadlag_delayed_hazard
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) (n : ℕ) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    let H := fun (ω : Ω) (i : Fin n) ↦ Γ i ω
    let L : Ω → WithTop ℝ≥0 :=
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let S := fun (ω : Ω) ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
    let κ := condDistrib S H P
    let D : ℝ≥0 → Ω → ℝ := stoppedProcess
      (fun (s : ℝ≥0) (v : Ω) ↦ if L v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ (H v)) (s - (L v).untopA)).toReal else 0) (Γ n)
    IsStronglyPredictable F D ∧ D 0 = 0 ∧
      ∀ᵐ ω ∂P, Monotone (fun t ↦ D t ω) ∧ IsCadlagPath (fun t ↦ D t ω) := by
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
    (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
  let H := fun (ω : Ω) (i : Fin n) ↦ Γ i ω
  let L : Ω → WithTop ℝ≥0 :=
    Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
  let S := fun (ω : Ω) ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
  let κ := condDistrib S H P
  let D : ℝ≥0 → Ω → ℝ := stoppedProcess
    (fun (s : ℝ≥0) (v : Ω) ↦ if L v ≤ (s : WithTop ℝ≥0)
      then (eCumulativeHazard (κ (H v)) (s - (L v).untopA)).toReal else 0) (Γ n)
  change IsStronglyPredictable F D ∧ D 0 = 0 ∧
    ∀ᵐ ω ∂P, Monotone (fun t ↦ D t ω) ∧ IsCadlagPath (fun t ↦ D t ω)
  have hinfo := isStoppingTime_and_measurable_history_natural_count hΓ hMeas
  obtain ⟨hL, hHist⟩ := hinfo.2 n
  have hp : IsStronglyPredictable F D :=
    isStronglyPredictable_stopped_delayed_eCumulativeHazard κ hL (hinfo.1 n)
      hHist (fun _ ↦ 0)
  refine ⟨hp, ?_, ?_⟩
  · funext ω
    change D 0 ω = 0
    exact stoppedProcess_delayed_eCumulativeHazard_eq_zero_of_le κ H
      (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ L ω from bot_le)
  · have hH : Measurable H := measurable_pi_lambda _ fun i : Fin n ↦ hMeas i
    have hS : Measurable S := measurable_arrivalInterarrival hMeas n
    let q := fun (t : ℝ≥0) ω ↦ t - (min (t : WithTop ℝ≥0) (L ω)).untopA
    have heq (ω : Ω) : (fun t ↦ D t ω) = fun t ↦ stoppedProcess
        (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal) S (q t ω) ω := by
      funext t
      simpa only [D, L, S, q, stoppedProcess, id_eq] using
        stoppedProcess_delayed_eCumulativeHazard_eq_arrivalInterarrival κ H hΓ n t ω
    filter_upwards [ae_stopped_eCumulativeHazard_condDistrib_elapsedTime_paths
      (P := P) hH hS L] with ω hω
    rw [heq ω]
    exact hω.2

end ProbabilityTheory.IsNonexplosiveArrivalSequence
