/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalHazardGapHistory
public import StochLean.Probability.Process.Counting.ArrivalHazardInterval

/-! # The actual compensator as completed hazards plus one pending hazard

The sole canonical compensator of the actual arrival count is its finite
sum of completed conditional-gap hazards plus the current pending hazard.
All conditional laws are the original native laws given actual preceding
gaps, computed before completion. The actual count selects the index, so
the initial interval and every arrival endpoint are included without a
shifted-index convention.

The general conditional-hazard series has already been identified with the
canonical compensator. A pointwise path identity supplies this finite formula;
no expected-count bound, candidate compensator or local-martingale hypothesis
is added. Completed gaps and the pending stage's preceding lifetime are
genuinely finite in the terms where they occur.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- The actual count compensator is the finite sum of completed hazards
and exactly one pending hazard, conditioned on actual gap history. The
formula holds at all times on one common event, including time zero and
every arrival endpoint, with the original probability kernels unchanged. -/
theorem predictableCompensator_count_eq_completed_add_pending_hazard
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    let G := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦
      arrivalInterarrival (fun j ↦ Γ j ω) i
    let L := fun n ↦
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun j ↦ Γ j ω) n
    let κ := fun n ↦ condDistrib (S n) (G n) P
    let hC := count_compensator_domain_natural_usual (P := P) hΓ hMeas
    Indistinguishable
      (hC.2.2.predictableCompensator hC.1 (F.usualAugmentation_isUsual P) hC.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
        let k := (hΓ ω).count t
        (∑ n ∈ Finset.range k,
          (eCumulativeHazard (κ n (G n ω)) (S n ω).untopA).toReal) +
        (eCumulativeHazard (κ k (G k ω)) (t - (L k ω).untopA)).toReal)
      P.completion := by
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  let G := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦
    arrivalInterarrival (fun j ↦ Γ j ω) i
  let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun j ↦ Γ j ω) n
  let κ := fun n ↦ condDistrib (S n) (G n) P
  refine (predictableCompensator_count_eq_conditional_gap_history_hazard_sum
    (P := P) hΓ hMeas).trans ?_
  exact ae_of_all _ fun ω t ↦ tsum_delayed_eCumulativeHazard_eq_completed_add_pending
    (fun n (v : Ω) ↦ κ n (G n v)) hΓ t ω

end ProbabilityTheory.IsNonexplosiveArrivalSequence
