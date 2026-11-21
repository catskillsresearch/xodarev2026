/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CauseSpecificHazardDensity
public import StochLean.Probability.Process.Counting.MarkedSingleJumpCompensator

/-! # The literal density integral for an actual marked single-jump compensator

The cause density represents the finite positive restrictions of the
actual marked submeasure. Its denominator remains the observation law's
closed survival. Positive closed survival at the observed lifetime holds
on one observation-law event and controls every finite stopped clock.
Thus the density-integral formula holds simultaneously at all times,
including samples whose observed lifetime is infinite.

On the original probability space, the marked submeasure is exactly
`(P.restrict B).map τ`. The true canonical compensator in the genuine usual
natural filtration of the observed pair is identified with the literal
density divided by observation survival integral. No alternative selector,
prematurely revealed mark, or candidate compensation assumption is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- Actual finite-restriction cause densities identify the stopped cause
hazard with its density/survival integral on one observation-law event,
simultaneously for all finite observation times. -/
theorem ae_forall_stopped_eCauseSpecificHazard_eq_density_integral
    (μ ρ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ] (hρ : ρ ≤ μ)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hden : ∀ T : ℝ≥0,
      (ρ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
          (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
            (fun x ↦ ENNReal.ofReal (f x)))
    (hfn : ∀ T : ℝ≥0, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)), 0 ≤ f x) :
    ∀ᵐ v ∂μ, ∀ t : ℝ≥0,
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal)
        id t v =
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
  exact (intervalIntegrable_cause_density_div_survival_and_integral_eq
    μ ρ hρ hf (hden u) (hfn u) hpos le_rfl).2.symm

open Classical in
/-- The original marked count's sole compensator is the literal stopped
cause-density integral, using the observation survival in the denominator
and the genuine usual natural filtration of both observed causes. -/
theorem predictableCompensator_markedSingleJumpCount_eq_density_integral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {τ : Ω → WithTop ℝ≥0} {B : Set Ω} {f : ℝ → ℝ}
    (hτ : Measurable τ) (hB : MeasurableSet B) (hf : Measurable f)
    (hden : ∀ T : ℝ≥0,
      (((P.restrict B).map τ).restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
          (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
            (fun x ↦ ENNReal.ofReal (f x)))
    (hfn : ∀ T : ℝ≥0, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)), 0 ≤ f x) :
    let F := Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)
    let hD := markedSingleJumpCount_compensator_domain (P := P) hτ hB
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦
        ∫ x in (0 : ℝ)..((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ),
          f x / (P.map τ).real (Ici (x.toNNReal : WithTop ℝ≥0)))
      P.completion := by
  let : IsProbabilityMeasure (P.map τ) :=
    Measure.isProbabilityMeasure_map hτ.aemeasurable
  have hρ : (P.restrict B).map τ ≤ P.map τ :=
    Measure.map_mono Measure.restrict_le_self hτ
  apply (predictableCompensator_markedSingleJumpCount_eq_stopped_cause_hazard
    (P := P) hτ hB).trans
  exact ae_of_ae_map (μ := P) hτ.aemeasurable
    (ae_forall_stopped_eCauseSpecificHazard_eq_density_integral
      (P.map τ) ((P.restrict B).map τ) hρ hf hden hfn)

end ProbabilityTheory
