/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardDensity
public import StochLean.Probability.Process.Counting.GeneralLifetimeHazard

/-! # The actual density-integral compensator on the original space

Densities of the finite positive restrictions of the actual lifetime law
identify its stopped hazard with the literal density divided by survival
integral. The original initial and infinite atoms remain in the survival
denominator. One observation-law event proves the identity for all times:
positive closed survival at the observed lifetime controls every finite
stopped clock, and the density identity is used only at that finite cap.

The original-space theorem then identifies the existing sole compensator
with that actual integral. It constructs no alternate compensator and assumes
neither a martingale remainder nor a desired primitive identity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- Actual finite-restriction densities identify the original stopped
hazard with the literal density/survival integral on one all-times event. -/
theorem ae_forall_stopped_eCumulativeHazard_eq_density_integral
    (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f)
    (hden : ∀ T : ℝ≥0,
      (μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
          (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
            (fun x ↦ ENNReal.ofReal (f x)))
    (hfn : ∀ T : ℝ≥0, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)), 0 ≤ f x) :
    ∀ᵐ v ∂μ, ∀ t : ℝ≥0,
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v =
        ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) v).untopA : ℝ),
          f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0)) := by
  filter_upwards [ae_pos_measure_Ici μ] with v hv t
  let u : ℝ≥0 := (min (t : WithTop ℝ≥0) v).untopA
  have hfinite : min (t : WithTop ℝ≥0) v ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hu : (u : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) v := by
    dsimp only [u]
    rw [WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]
  have hpos : 0 < μ (Ici (u : WithTop ℝ≥0)) :=
    hv.trans_le (measure_mono (Ici_subset_Ici.mpr (hu.le.trans (min_le_right _ _))))
  exact (intervalIntegrable_density_div_survival_and_integral_eq
    μ hf (hden u) (hfn u) hpos le_rfl).2.symm

/-- The original count's selected compensator is its actual density over
survival integral, in the genuine usual natural augmentation. Infinite
lifetimes and an initial atom are not excluded. -/
theorem predictableCompensator_singleJumpCount_eq_density_integral_map
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {τ : Ω → WithTop ℝ≥0} {f : ℝ → ℝ} (hτ : Measurable τ) (hf : Measurable f)
    (hden : ∀ T : ℝ≥0,
      ((P.map τ).restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
          (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
            (fun x ↦ ENNReal.ofReal (f x)))
    (hfn : ∀ T : ℝ≥0, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)), 0 ≤ f x) :
    let F := Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)
    let hD := singleJumpCount_compensator_domain_map (P := P) hτ
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦
        ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ),
          f x / (P.map τ).real (Ici (x.toNNReal : WithTop ℝ≥0)))
      P.completion := by
  let : IsProbabilityMeasure (P.map τ) :=
    Measure.isProbabilityMeasure_map hτ.aemeasurable
  apply (predictableCompensator_singleJumpCount_eq_stopped_hazard_map
    (P := P) hτ).trans
  exact ae_of_ae_map (μ := P) hτ.aemeasurable
    (ae_forall_stopped_eCumulativeHazard_eq_density_integral
      (P.map τ) hf hden hfn)

end ProbabilityTheory
