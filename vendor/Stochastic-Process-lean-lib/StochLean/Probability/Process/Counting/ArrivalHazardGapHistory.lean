/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalHazardCompensator
public import StochLean.Probability.Process.Counting.ConditionalArrivalInformation

/-! # The actual count compensator conditioned on actual gap history

The first `n` original arrivals and the first `n` actual absorbing gaps
generate exactly the same information. Their evaluated native conditional
gap laws therefore agree as measures on a single event for all countably
many stages. The original delayed hazard series is unchanged on that event
at every calendar time, including the first stage and infinite arrival tails.

The actual canonical compensator and its domain are those already constructed
for the original count in its genuine usual natural augmentation. All
conditional kernels here are still computed under the original measure and
sample space, not recomputed after completion. No independence of absorbing
gaps, alternate compensator or candidate martingale is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- The sole count compensator is the original delayed hazard series
conditioned on preceding actual gaps. The kernels are computed before
completion; equality holds for all times on one common almost-sure event. -/
theorem predictableCompensator_count_eq_conditional_gap_history_hazard_sum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    let G := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦
      arrivalInterarrival (fun k ↦ Γ k ω) i
    let L := fun n ↦
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
    let κ := fun n ↦ condDistrib (S n) (G n) P
    let D : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ stoppedProcess
      (fun (s : ℝ≥0) (ω : Ω) ↦ if L n ω ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ n (G n ω)) (s - (L n ω).untopA)).toReal else 0) (Γ n)
    let hC := count_compensator_domain_natural_usual (P := P) hΓ hMeas
    Indistinguishable
      (hC.2.2.predictableCompensator hC.1 (F.usualAugmentation_isUsual P) hC.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ∑' n, D n t ω)
      P.completion := by
  classical
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  let H := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦ Γ i ω
  let G := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦
    arrivalInterarrival (fun k ↦ Γ k ω) i
  let L := fun n ↦
    Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
  let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
  let κ := fun n ↦ condDistrib (S n) (H n) P
  let η := fun n ↦ condDistrib (S n) (G n) P
  let D : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ stoppedProcess
    (fun (s : ℝ≥0) (ω : Ω) ↦ if L n ω ≤ (s : WithTop ℝ≥0)
      then (eCumulativeHazard (κ n (H n ω)) (s - (L n ω).untopA)).toReal else 0) (Γ n)
  let E : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ stoppedProcess
    (fun (s : ℝ≥0) (ω : Ω) ↦ if L n ω ≤ (s : WithTop ℝ≥0)
      then (eCumulativeHazard (η n (G n ω)) (s - (L n ω).untopA)).toReal else 0) (Γ n)
  refine (predictableCompensator_count_eq_conditional_hazard_sum (P := P) hΓ hMeas).trans ?_
  change ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∑' n, D n t ω) = ∑' n, E n t ω
  have hk (n : ℕ) : (fun ω ↦ κ n (H n ω)) =ᵐ[P] fun ω ↦ η n (G n ω) :=
    condDistrib_arrivalInterarrival_history_ae_eq hΓ hMeas n
  filter_upwards [ae_all_iff.mpr hk] with ω hω t
  apply tsum_congr
  intro n
  simp only [D, E, stoppedProcess, hω n]

end ProbabilityTheory.IsNonexplosiveArrivalSequence
