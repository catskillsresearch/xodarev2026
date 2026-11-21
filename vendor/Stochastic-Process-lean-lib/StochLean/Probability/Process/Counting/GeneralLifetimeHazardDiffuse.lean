/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.GeneralLifetimeHazard
public import StochLean.Probability.Process.Counting.HazardContinuousPaths
public import StochLean.Probability.Process.Counting.HazardLogarithm

/-! # The continuous logarithmic compensator of an arbitrary diffuse lifetime

The lifetime lives on the original probability space, and diffuseness is a
property of its actual pushforward law. The canonical lifetime-space results
pull back to a single full-measure event on which the original stopped hazard
is continuous and has its logarithmic CDF formula at every finite time.

Null singletons exclude both zero and infinite lifetime atoms. In particular,
the real pushforward used by the native CDF represents the actual finite
lifetime almost surely. The logarithm identity uses the already established
positive sampled survival event; it does not interpret `log 0` or a real
conversion of an infinite hazard as a cumulative hazard.

The final statement identifies the existing sole predictable compensator in
the genuine usual augmentation of the original closed-count natural
filtration. Neither a second compensator nor a second process-domain owner is
introduced, and no absolute-continuity or density assumption is needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0}
  [NullSingletonClass (P.map τ)]

/-- A lifetime with diffuse actual law has continuous original stopped
hazard paths on one common full-measure event. -/
theorem hasContinuousPaths_stopped_eCumulativeHazard_map (hτ : Measurable τ) :
    HasContinuousPaths (stoppedProcess
      (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ) P := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  exact ae_of_ae_map (μ := P) hτ.aemeasurable
    (hasContinuousPaths_stopped_eCumulativeHazard (P.map τ))

/-- The original stopped hazard has the logarithmic CDF formula at every
finite observation time on a single full-measure event. -/
theorem ae_forall_stopped_eCumulativeHazard_eq_neg_log_cdf_map (hτ : Measurable τ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      stoppedProcess (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ t ω =
        -Real.log (1 - cdf ((P.map τ).map (fun w : WithTop ℝ≥0 ↦ (w.untopA : ℝ)))
          (((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ≥0) : ℝ)) := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  exact ae_of_ae_map (μ := P) hτ.aemeasurable
    (ae_forall_stopped_eCumulativeHazard_eq_neg_log_cdf (P.map τ))

/-- The already selected compensator of the original closed count equals
the actual logarithmic hazard in its genuine usual natural filtration. -/
theorem predictableCompensator_singleJumpCount_eq_neg_log_cdf_map (hτ : Measurable τ) :
    let F := Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)
    let hD := singleJumpCount_compensator_domain_map (P := P) hτ
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
        -Real.log (1 - cdf ((P.map τ).map (fun w : WithTop ℝ≥0 ↦ (w.untopA : ℝ)))
          (((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ≥0) : ℝ)))
      P.completion := by
  exact (predictableCompensator_singleJumpCount_eq_stopped_hazard_map (P := P) hτ).trans
    (ae_forall_stopped_eCumulativeHazard_eq_neg_log_cdf_map (P := P) hτ)

end ProbabilityTheory
