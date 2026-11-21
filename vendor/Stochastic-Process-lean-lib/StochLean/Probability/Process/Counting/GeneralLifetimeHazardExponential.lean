/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.GeneralLifetimeHazard
public import StochLean.Probability.Process.Counting.HazardExponentialLaw

/-! # The rate-correct compensator of an exponential lifetime

The original lifetime may live on any probability space. Its actual real
pushforward is assumed to be Mathlib's exponential law of positive rate
`r`. The actual extended lifetime law then has the exponential cumulative
hazard `r*t`, and the original stopped hazard is exactly `r*(t ∧ τ)`.

Every stopped clock is finite because the observation time is finite. This
is proved before using its finite coordinate, even at samples where the
original lifetime is infinite. No separate almost-sure finiteness premise,
hazard certificate, or compensator choice is supplied.

The compensator conclusion refers to the existing unique compensator in
the genuinely completed usual natural filtration, with no change of owner.
The factor `r` is retained; only the unit-rate case simplifies to `t ∧ τ`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0} {r : ℝ}

/-- The original stopped hazard is pointwise the rate times the actual
stopped finite clock, including samples with an infinite lifetime. -/
theorem stopped_eCumulativeHazard_map_eq_rate_mul_stoppedClock
    (hτ : Measurable τ) (hr : 0 < r)
    (hlaw : P.map (fun ω ↦ ((τ ω).untopA : ℝ)) = expMeasure r) :
    stoppedProcess (fun s (_ : Ω) ↦ (eCumulativeHazard (P.map τ) s).toReal) τ =
      fun (t : ℝ≥0) ω ↦ r * ((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ) := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  have hφ : Measurable (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hmap : (P.map τ).map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
      expMeasure r := by
    rw [Measure.map_map hφ hτ]
    exact hlaw
  funext t ω
  have hfinite : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  change (eCumulativeHazard (P.map τ) (min (t : WithTop ℝ≥0) (τ ω)).untopA).toReal =
    r * ((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ)
  rw [WithTop.untopA_eq_untop hfinite]
  exact eCumulativeHazard_toReal_of_map_untopA_eq_expMeasure (P.map τ) hr hmap _

/-- The actual sole compensator of an exponential closed count is the
rate-correct stopped clock in the genuinely usual completed natural filtration. -/
theorem predictableCompensator_singleJumpCount_eq_rate_mul_stoppedClock
    (hτ : Measurable τ) (hr : 0 < r)
    (hlaw : P.map (fun ω ↦ ((τ ω).untopA : ℝ)) = expMeasure r) :
    let F := Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)
    let hD := singleJumpCount_compensator_domain_map (P := P) hτ
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
        r * ((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ)) P.completion := by
  refine (predictableCompensator_singleJumpCount_eq_stopped_hazard_map (P := P) hτ).trans ?_
  apply ae_of_all
  intro ω t
  exact congrFun (congrFun
    (stopped_eCumulativeHazard_map_eq_rate_mul_stoppedClock (P := P) hτ hr hlaw) t) ω

end ProbabilityTheory
