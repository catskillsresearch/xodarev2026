/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.GeneralLifetimeHazard
public import StochLean.Probability.Process.Counting.HazardAbsolutelyContinuous

/-! # Absolutely continuous hazard compensators on the original sample space

Absolute continuity is assumed only for the actual finite positive lifetime
law, restricted before it is mapped into real time. The canonical stopped
hazard's common-event absolute continuity pulls back to the original sample
space along the measurable lifetime.

The existing unique compensator is indistinguishable from that original
stopped hazard in the genuinely usual completed natural filtration. On one
common event their entire paths coincide, so the native real-interval
absolute continuity also holds for the actual selected compensator.

No density, finite-lifetime assumption, compensator continuity certificate,
new path-regularity predicate, or compensator selector is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0}

/-- Absolute continuity of the actual finite positive lifetime law gives
absolute continuity of every original stopped-hazard path on one common event. -/
theorem ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard_map
    (hτ : Measurable τ)
    (hAC : ∀ T : ℝ≥0,
      ((P.map τ).restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume) :
    ∀ᵐ ω ∂P, ∀ S : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun x : ℝ ↦ stoppedProcess
        (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ x.toNNReal ω)
      0 (S : ℝ) := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  exact ae_of_ae_map hτ.aemeasurable
    (ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard (P.map τ) hAC)

/-- The actual sole compensator has locally absolutely continuous paths on
one common event in the genuine usual completion, without any density input. -/
theorem ae_forall_absolutelyContinuousOnInterval_singleJumpCount_compensator_map
    (hτ : Measurable τ)
    (hAC : ∀ T : ℝ≥0,
      ((P.map τ).restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume) :
    let F := Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)
    let hD := singleJumpCount_compensator_domain_map (P := P) hτ
    let A := hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
      (F.usualAugmentation_isUsual P) hD.2.1
    ∀ᵐ (ω : NullMeasurableSpace Ω P) ∂P.completion, ∀ S : ℝ≥0,
      AbsolutelyContinuousOnInterval (fun x : ℝ ↦ A x.toNNReal ω) 0 (S : ℝ) := by
  let F := Filtration.natural
    (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount hτ)
  let hD := singleJumpCount_compensator_domain_map (P := P) hτ
  let A := hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
    (F.usualAugmentation_isUsual P) hD.2.1
  have he := predictableCompensator_singleJumpCount_eq_stopped_hazard_map (P := P) hτ
  have hc : ∀ᵐ (ω : NullMeasurableSpace Ω P) ∂P.completion, ∀ S : ℝ≥0,
      AbsolutelyContinuousOnInterval
        (fun x : ℝ ↦ stoppedProcess
          (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ x.toNNReal ω)
        0 (S : ℝ) :=
    ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard_map
      (Ω := Ω) (mΩ := mΩ) (P := P) (τ := τ) hτ hAC
  change ∀ᵐ (ω : NullMeasurableSpace Ω P) ∂P.completion, ∀ S : ℝ≥0,
    AbsolutelyContinuousOnInterval (fun x : ℝ ↦ A x.toNNReal ω) 0 (S : ℝ)
  filter_upwards [he, hc] with ω hω hpath
  intro S
  have hfun : (fun x : ℝ ↦ A x.toNNReal ω) = fun x : ℝ ↦ stoppedProcess
      (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ x.toNNReal ω :=
    funext fun x ↦ hω x.toNNReal
  rw [hfun]
  exact hpath S

end ProbabilityTheory
