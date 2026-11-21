/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalConditionalIndependent
public import StochLean.Probability.Process.Counting.ArrivalHazardCompensator

/-! # Marginal hazards for independent latent arrival durations

Independent positive latent durations with diverging literal prefix sums
construct the original nonexplosive arrival count. Its sole canonical
compensator, in the genuine usual natural augmentation, is the sum of the
actual delayed, stopped hazards of the original marginal duration laws.

The conditional-gap law is replaced by its marginal only on the finite
preceding-prefix event. A stage activated at a finite stopped clock necessarily
belongs to this event. After an infinite preceding arrival the stage remains
zero; no independence assertion is made for the absorbing actual gaps there.
A countable intersection gives one common event for all stages and all times.

All marginal and conditional laws are computed under the original probability
measure, before completion. The original count, hazard, stopping operation and
canonical compensator are retained, with no second selector or assumed
compensation certificate. Infinite durations and absorbing arrival tails are
allowed. The marginal series agrees termwise with the already constructed
conditional-hazard series on that common event.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- For independent positive latent durations, the existing canonical count
compensator is the actual sum of delayed, stopped marginal hazards. Only
literal prefix nonexplosion is required; infinite durations remain allowed. -/
theorem predictableCompensator_count_prefix_eq_marginal_hazard_sum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ → Ω → WithTop ℝ≥0} (hd : ∀ n, Measurable (d n))
    (hind : iIndepFun d P) (hpos : ∀ ω n, 0 < d n ω)
    (hdiv : ∀ ω,
      Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), d i ω) atTop (𝓝 ⊤)) :
    let : MeasurableAdd₂ (WithTop ℝ≥0) := inferInstanceAs (MeasurableAdd₂ ℝ≥0∞)
    let Γ : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ ∑ i ∈ Finset.range (n + 1), d i ω
    let hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω) := fun ω ↦
      isNonexplosiveArrivalSequence_sum_range_of_pos (fun n ↦ d n ω) (hpos ω) (hdiv ω)
    let hMeasΓ : ∀ n, Measurable (Γ n) := fun n ↦
      (Finset.range (n + 1)).measurable_fun_sum fun i _ ↦ hd i
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (IsNonexplosiveArrivalSequence.measurable_count hΓ hMeasΓ s).stronglyMeasurable)
    let L := fun n ↦
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let D := fun n ↦ stoppedProcess
      (fun (s : ℝ≥0) (ω : Ω) ↦ if L n ω ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (P.map (d n)) (s - (L n ω).untopA)).toReal else 0) (Γ n)
    let hC := IsNonexplosiveArrivalSequence.count_compensator_domain_natural_usual
      (P := P) hΓ hMeasΓ
    Indistinguishable
      (hC.2.2.predictableCompensator hC.1 (F.usualAugmentation_isUsual P) hC.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ∑' n, D n t ω)
      P.completion := by
  classical
  intro hAdd Γ hΓ hMeasΓ F L D hC
  let : MeasurableAdd₂ (WithTop ℝ≥0) := hAdd
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  let H := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦ Γ i ω
  let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
  let κ := fun n ↦ condDistrib (S n) (H n) P
  let A := fun n ↦ stoppedProcess
    (fun (s : ℝ≥0) (ω : Ω) ↦ if L n ω ≤ (s : WithTop ℝ≥0)
      then (eCumulativeHazard (κ n (H n ω)) (s - (L n ω).untopA)).toReal else 0) (Γ n)
  have hconditional : Indistinguishable
      (hC.2.2.predictableCompensator hC.1 (F.usualAugmentation_isUsual P) hC.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ∑' n, A n t ω)
      P.completion :=
    IsNonexplosiveArrivalSequence.predictableCompensator_count_eq_conditional_hazard_sum
      hΓ hMeasΓ
  refine hconditional.trans ?_
  have hlaw (n : ℕ) : ∀ᵐ ω ∂P, (∑ i ∈ Finset.range n, d i ω) ≠ ⊤ →
      κ n (H n ω) = P.map (d n) :=
    condDistrib_arrivalInterarrival_eq_marginal_of_iIndepFun hd hind n
  have hcommon : ∀ᵐ ω ∂P, ∀ n, (∑ i ∈ Finset.range n, d i ω) ≠ ⊤ →
      κ n (H n ω) = P.map (d n) := ae_all_iff.mpr hlaw
  have hcompleted : ∀ᵐ ω ∂P.completion, ∀ n, (∑ i ∈ Finset.range n, d i ω) ≠ ⊤ →
      κ n (H n ω) = P.map (d n) := hcommon
  filter_upwards [hcompleted] with ω hω
  intro t
  apply tsum_congr
  intro n
  let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (Γ n ω)).untopA
  change (if L n ω ≤ (u : WithTop ℝ≥0)
      then (eCumulativeHazard (κ n (H n ω)) (u - (L n ω).untopA)).toReal else 0) =
    (if L n ω ≤ (u : WithTop ℝ≥0)
      then (eCumulativeHazard (P.map (d n)) (u - (L n ω).untopA)).toReal else 0)
  by_cases hactive : L n ω ≤ (u : WithTop ℝ≥0)
  · have hL : L n ω = ∑ i ∈ Finset.range n, d i ω := by
      cases n with
      | zero =>
          change (0 : WithTop ℝ≥0) = ∑ i ∈ Finset.range 0, d i ω
          simp only [Finset.range_zero, Finset.sum_empty]
      | succ k => rfl
    have hfinite : (∑ i ∈ Finset.range n, d i ω) ≠ ⊤ := by
      rw [← hL]
      exact ne_top_of_le_ne_top WithTop.coe_ne_top hactive
    rw [if_pos hactive, if_pos hactive, hω n hfinite]
  · rw [if_neg hactive, if_neg hactive]

end ProbabilityTheory
