/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.IndependentArrivalHazard
public import StochLean.Probability.Process.Counting.ArrivalPrefixHazardInterval

/-! # The corrected independent-interval compensator formula

Independent positive latent durations with nonexplosive prefix sums give the
actual count. Its sole compensator is the finite sum of completed marginal
hazards plus the current marginal hazard at its elapsed age. The count index
includes the initial interval, and all completed durations are retained.

This corrects the omitted first interval and shifted completed-sum index in
the printed corollary to Protter III.23. Infinite durations remain allowed:
latent-gap recovery is used only for completed stages with finite past, and
no independence of absorbing gaps after an infinite arrival is asserted.
All marginal laws are those of the original probability measure.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- The sole actual count compensator has the corrected independent
completed-plus-pending marginal-hazard formula, including the first interval
and every arrival endpoint. No compensation certificate is an input. -/
theorem predictableCompensator_count_prefix_eq_completed_add_pending_marginal_hazard
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
    let hC := IsNonexplosiveArrivalSequence.count_compensator_domain_natural_usual
      (P := P) hΓ hMeasΓ
    Indistinguishable
      (hC.2.2.predictableCompensator hC.1 (F.usualAugmentation_isUsual P) hC.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
        let k := (hΓ ω).count t
        (∑ n ∈ Finset.range k, (eCumulativeHazard (P.map (d n)) (d n ω).untopA).toReal) +
        (eCumulativeHazard (P.map (d k))
          (t - (∑ j ∈ Finset.range k, d j ω).untopA)).toReal)
      P.completion := by
  intro hAdd Γ hΓ hMeasΓ F hC
  let : MeasurableAdd₂ (WithTop ℝ≥0) := hAdd
  refine (predictableCompensator_count_prefix_eq_marginal_hazard_sum
    hd hind hpos hdiv).trans ?_
  exact ae_of_all _ fun ω t ↦
    tsum_delayed_eCumulativeHazard_prefix_eq_completed_add_pending
      d (fun n ↦ P.map (d n)) hΓ t ω

end ProbabilityTheory
