/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CauseSpecificHazard
public import StochLean.ForMathlib.MeasureTheory.OrderSurvival
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-! # Actual stopped cause-hazard expectation and increment balance

The observation law supplies the stopping lifetime and the pre-jump
survival denominator. Its actual dominated cause submeasure supplies the
hazard integral. Tonelli's theorem therefore integrates the lifetime cutoff
against the observation law and the hazard time against the cause law.

Domination first proves that the cause law is finite and absolutely
continuous with respect to the observation law. Positive closed survival
at almost every observation consequently holds at almost every cause time,
so the reciprocal cancels genuinely, without a deterministic survival guard.
Only after the resulting finite extended expectation is proved do we pass
to the actual real stopped hazard and its L1 expectation.

The strict-survival increment balance follows from the two actual means:
off strict survival, both stopped clocks already coincide. Initial and
infinite atoms are retained in both laws; the hazard charges only finite
positive cause times. Neither law is required to be a probability measure.
These are integral identities, not an assumed compensator or martingale
certificate, and no new hazard or stopped-process owner is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable (μ ρ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ]

/-- The actual stopped extended cause hazard integrates to the finite
positive cause mass, without a deterministic positive-survival guard. -/
theorem lintegral_stoppedProcess_eCauseSpecificHazard (hρ : ρ ≤ μ) (t : ℝ≥0) :
    (∫⁻ v, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id t v ∂μ) =
      ρ (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  classical
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρ
  have hρμ : ρ ≪ μ := Measure.absolutelyContinuous_of_le hρ
  have hpositive : ∀ᵐ u ∂ρ, 0 < μ (Ici u) := hρμ.ae_le (ae_pos_measure_Ici μ)
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
        (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id t v ∂μ) =
        ∫⁻ v, ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), f v u ∂ρ ∂μ := by
      apply lintegral_congr
      intro v
      exact stoppedProcess_eCauseSpecificHazard_eq_lintegral μ ρ t v
    _ = ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0),
        ∫⁻ v, f v u ∂μ ∂ρ := lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ _ in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), (1 : ℝ≥0∞) ∂ρ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hpositive] with u hu
      have he : (fun v ↦ f v u) = (Ici u).indicator (fun _ ↦ w u) := by
        funext v
        simp only [f, indicator_apply, mem_Iic, mem_Ici]
      rw [he, lintegral_indicator_const measurableSet_Ici]
      exact ENNReal.inv_mul_cancel hu.ne' (measure_ne_top μ _)
    _ = _ := setLIntegral_one _

/-- The original real stopped cause hazard is L1 and has the actual cause
occurrence mean. Its extended value is first proved finite almost surely. -/
theorem integrable_stoppedProcess_eCauseSpecificHazard (hρ : ρ ≤ μ) (t : ℝ≥0) :
    Integrable (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id t) μ ∧
      (∫ v, stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id t v ∂μ) =
        ρ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρ
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id t
  have hm : Measurable A := (measurable_eCauseSpecificHazard μ ρ).comp
    ((measurable_const.min measurable_id).untopA)
  have he : (∫⁻ v, A v ∂μ) = ρ (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) :=
    lintegral_stoppedProcess_eCauseSpecificHazard μ ρ hρ t
  have hfinite : (∫⁻ v, A v ∂μ) ≠ ∞ := by
    rw [he]
    exact measure_ne_top ρ _
  have hA : ∀ᵐ v ∂μ, A v < ∞ := ae_lt_top hm hfinite
  change Integrable (fun v ↦ (A v).toReal) μ ∧
    (∫ v, (A v).toReal ∂μ) = ρ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0))
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite, ?_⟩
  rw [integral_toReal hm.aemeasurable hA, he]
  rfl

/-- On the observation's strict survival event at `s`, the true mean
cause-hazard increment is exactly the cause mass in `(s,t]`. -/
theorem setIntegral_stoppedProcess_eCauseSpecificHazard_toReal_sub
    (hρ : ρ ≤ μ) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ v in Ioi (s : WithTop ℝ≥0),
      (stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id t v -
      stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id s v) ∂μ) =
      ρ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  classical
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρ
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id
  have hAt : Integrable (A t) μ ∧ (∫ v, A t v ∂μ) =
      ρ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) :=
    integrable_stoppedProcess_eCauseSpecificHazard μ ρ hρ t
  have hAs : Integrable (A s) μ ∧ (∫ v, A s v ∂μ) =
      ρ.real (Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0)) :=
    integrable_stoppedProcess_eCauseSpecificHazard μ ρ hρ s
  have he : (Ioi (s : WithTop ℝ≥0)).indicator (fun v ↦ A t v - A s v) =
      fun v ↦ A t v - A s v := by
    funext v
    by_cases hv : (s : WithTop ℝ≥0) < v
    · exact indicator_of_mem (show v ∈ Ioi (s : WithTop ℝ≥0) from hv)
        (fun v ↦ A t v - A s v)
    · have hnot : v ∉ Ioi (s : WithTop ℝ≥0) := hv
      rw [indicator_of_notMem hnot]
      have hvs : v ≤ (s : WithTop ℝ≥0) := le_of_not_gt hv
      symm
      dsimp only [A]
      rw [stoppedProcess_eq_of_ge (hvs.trans (WithTop.coe_le_coe.mpr hst)),
        stoppedProcess_eq_of_ge hvs, sub_self]
  have hsets : Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0) \
      Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0) =
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    ext v
    simp only [Set.mem_sdiff, mem_Ioc]
    constructor
    · intro h
      exact ⟨lt_of_not_ge (fun hvs ↦ h.2 ⟨h.1.1, hvs⟩), h.1.2⟩
    · intro h
      exact ⟨⟨(WithTop.coe_le_coe.mpr (show (0 : ℝ≥0) ≤ s from bot_le)).trans_lt h.1, h.2⟩,
        fun hvs ↦ not_lt_of_ge hvs.2 h.1⟩
  change (∫ v in Ioi (s : WithTop ℝ≥0), A t v - A s v ∂μ) = _
  calc
    (∫ v in Ioi (s : WithTop ℝ≥0), A t v - A s v ∂μ) =
        ∫ v, A t v - A s v ∂μ := by rw [← integral_indicator measurableSet_Ioi, he]
    _ = (∫ v, A t v ∂μ) - ∫ v, A s v ∂μ := integral_sub hAt.1 hAs.1
    _ = ρ.real (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) -
        ρ.real (Ioc (0 : WithTop ℝ≥0) (s : WithTop ℝ≥0)) := by rw [hAt.2, hAs.2]
    _ = ρ.real (Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
      rw [← measureReal_sdiff
        (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst)) measurableSet_Ioc, hsets]

end ProbabilityTheory
