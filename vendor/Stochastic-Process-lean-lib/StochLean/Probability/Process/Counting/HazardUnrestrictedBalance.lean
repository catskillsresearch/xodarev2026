/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardBalance
public import StochLean.ForMathlib.MeasureTheory.OrderSurvival

/-! # Actual stopped-hazard expectation without a support-endpoint guard

At almost every lifetime the pre-jump survival mass is positive, including
any atom at the last possible lifetime. Thus the Tonelli cancellation needs
no positive-survival assumption at an arbitrary deterministic horizon.
The extended expectation is finite for a finite lifetime measure. Only
after this is proved do we convert the actual stopped hazard to real values.

These are expectation and integrability results for the existing stopped
process. They do not assert pointwise finiteness at every possible sample,
nor common-event cadlag regularity or a general compensation theorem.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ]

/-- The actual extended stopped-hazard mean, including when deterministic
observation lies at or beyond a zero-survival support endpoint. -/
theorem lintegral_stoppedProcess_eCumulativeHazard_unrestricted (t : ℝ≥0) :
    (∫⁻ v, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v ∂μ) =
      μ (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  classical
  let w : WithTop ℝ≥0 → ℝ≥0∞ := fun u ↦ (μ (Ici u))⁻¹
  let f : WithTop ℝ≥0 → WithTop ℝ≥0 → ℝ≥0∞ := fun v ↦ (Iic v).indicator w
  have hw : Measurable w := by
    have ha : Antitone (fun u : WithTop ℝ≥0 ↦ μ (Ici u)) :=
      fun _ _ huv ↦ measure_mono (Ici_subset_Ici.mpr huv)
    exact ha.measurable.inv
  have hf : Measurable (Function.uncurry f) := by
    have hm : Measurable (fun p : WithTop ℝ≥0 × WithTop ℝ≥0 ↦
        if p.2 ≤ p.1 then w p.2 else 0) :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hw.comp measurable_snd) measurable_const
    convert hm using 1
    funext p
    change (Iic p.1).indicator w p.2 = _
    simp only [indicator_apply, mem_Iic]
  calc
    (∫⁻ v, stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v ∂μ) =
        ∫⁻ v, ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), f v u ∂μ ∂μ := by
      apply lintegral_congr
      intro v
      exact stoppedProcess_eCumulativeHazard_eq_lintegral μ t v
    _ = ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0),
        ∫⁻ v, f v u ∂μ ∂μ := lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ _ in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_pos_measure_Ici μ)] with u hu
      have he : (fun v ↦ f v u) = (Ici u).indicator (fun _ ↦ w u) := by
        funext v
        simp only [f, indicator_apply, mem_Iic, mem_Ici]
      rw [he, lintegral_indicator_const measurableSet_Ici]
      exact ENNReal.inv_mul_cancel hu.ne' (measure_ne_top μ _)
    _ = _ := setLIntegral_one _

/-- The actual real stopped hazard is L1 and has the occurrence-mass mean.
Extended finiteness is established almost surely before applying `toReal`. -/
theorem integrable_stoppedProcess_eCumulativeHazard_unrestricted (t : ℝ≥0) :
    Integrable (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t) μ ∧
      (∫ v, stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v ∂μ) =
        μ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t
  have hm : Measurable A := (measurable_eCumulativeHazard μ).comp
    ((measurable_const.min measurable_id).untopA)
  have he : (∫⁻ v, A v ∂μ) = μ (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) :=
    lintegral_stoppedProcess_eCumulativeHazard_unrestricted μ t
  have hfinite : (∫⁻ v, A v ∂μ) ≠ ∞ := by
    rw [he]
    exact measure_ne_top μ _
  have hA : ∀ᵐ v ∂μ, A v < ∞ := ae_lt_top hm hfinite
  change Integrable (fun v ↦ (A v).toReal) μ ∧
    (∫ v, (A v).toReal ∂μ) = μ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0))
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite, ?_⟩
  rw [integral_toReal hm.aemeasurable hA, he]
  rfl

end ProbabilityTheory
