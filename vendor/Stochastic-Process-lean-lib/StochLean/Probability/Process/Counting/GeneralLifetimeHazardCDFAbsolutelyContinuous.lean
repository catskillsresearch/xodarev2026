/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.GeneralLifetimeHazardAbsolutelyContinuous
public import StochLean.Probability.Process.Counting.HazardCDFAbsolutelyContinuous

/-! # The CDF absolute-continuity corollary on the original probability space

The input is the actual original-space lifetime CDF, absolutely continuous
on every finite nonnegative interval, together with almost-sure finiteness
of that lifetime. The previously verified derivative/FTC measure bridge
constructs the required absolutely continuous finite lifetime restrictions.

Both the original stopped hazard and the already selected canonical
compensator have locally absolutely continuous paths on one common event.
The latter is on the genuine usual completion, not an assumed completed
version of the original measurable space. No density or compensator-path
regularity certificate is taken as input.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0}

private theorem absolutelyContinuous_restricted_law_of_source_cdf
    (hτ : Measurable τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (cdf (P.map (fun ω ↦ ((τ ω).untopA : ℝ)))) 0 (T : ℝ)) :
    ∀ T : ℝ≥0, ((P.map τ).restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
      (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  have hTop : (P.map τ) {⊤} = 0 := by
    rw [Measure.map_apply hτ (measurableSet_singleton ⊤)]
    change P {ω | τ ω = ⊤} = 0
    simpa only [not_not] using (ae_iff.mp hfinite)
  have hφ : Measurable (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_id.untopA
  intro T
  apply absolutelyContinuous_map_restrict_lifetime_of_cdf (P.map τ) hTop T
  simpa only [Measure.map_map hφ hτ, Function.comp_def] using hAC T

/-- The source CDF absolute-continuity hypothesis gives actual stopped
hazard paths that are absolutely continuous on every compact interval. -/
theorem ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard_map_of_cdf
    (hτ : Measurable τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (cdf (P.map (fun ω ↦ ((τ ω).untopA : ℝ)))) 0 (T : ℝ)) :
    ∀ᵐ ω ∂P, ∀ S : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun x : ℝ ↦ stoppedProcess
        (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ x.toNNReal ω)
      0 (S : ℝ) :=
  ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard_map hτ
    (absolutelyContinuous_restricted_law_of_source_cdf hτ hfinite hAC)

/-- Protter III.21's absolute-continuity corollary for the actual selected
compensator, from the original finite lifetime and its actual CDF alone. -/
theorem ae_forall_absolutelyContinuousOnInterval_singleJumpCount_compensator_map_of_cdf
    (hτ : Measurable τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (cdf (P.map (fun ω ↦ ((τ ω).untopA : ℝ)))) 0 (T : ℝ)) :
    let F := Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)
    let hD := singleJumpCount_compensator_domain_map (P := P) hτ
    let A := hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
      (F.usualAugmentation_isUsual P) hD.2.1
    ∀ᵐ (ω : NullMeasurableSpace Ω P) ∂P.completion, ∀ S : ℝ≥0,
      AbsolutelyContinuousOnInterval (fun x : ℝ ↦ A x.toNNReal ω) 0 (S : ℝ) :=
  ae_forall_absolutelyContinuousOnInterval_singleJumpCount_compensator_map hτ
    (absolutelyContinuous_restricted_law_of_source_cdf hτ hfinite hAC)

end ProbabilityTheory
