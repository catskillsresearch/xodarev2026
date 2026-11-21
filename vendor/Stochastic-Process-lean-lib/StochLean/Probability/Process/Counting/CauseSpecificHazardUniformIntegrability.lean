/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CauseSpecificHazardBalance
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # Global uniform integrability of the stopped cause hazard

For a finite observation law and an actual dominated cause submeasure,
the integer-time supremum of the extended stopped cause hazard has integral
at most the total cause mass. Monotone convergence and the actual stopped
expectation establish this bound without a positive-survival cap.

Only after proving that supremum finite almost everywhere do we take its
real value. It is one integrable envelope for every finite-time stopped
cause hazard, which proves uniform integrability over the entire halfline.
The supremum is a local proof expression, not a new hazard or terminal owner.
Neither measure is assumed to be a probability measure.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- The actual real cause hazard stopped at the observation lifetime is
uniformly integrable over the whole halfline under any finite observation
law. The cause law is an actual dominated submeasure, not a normalized law. -/
theorem uniformIntegrable_stoppedProcess_eCauseSpecificHazard
    (μ ρ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ] (hρ : ρ ≤ μ) :
    UniformIntegrable (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id) 1 μ := by
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρ
  let H : ℝ≥0 → WithTop ℝ≥0 → ℝ≥0∞ :=
    stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id
  let Hinf : WithTop ℝ≥0 → ℝ≥0∞ := fun v ↦ ⨆ n : ℕ, H (n : ℝ≥0) v
  have hm (t : ℝ≥0) : Measurable (H t) :=
    (measurable_eCauseSpecificHazard μ ρ).comp
      ((measurable_const.min measurable_id).untopA)
  have hmono (v : WithTop ℝ≥0) : Monotone (fun t : ℝ≥0 ↦ H t v) := by
    intro s t hst
    change stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id s v ≤
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id t v
    rw [stoppedProcess_eCauseSpecificHazard_eq_lintegral μ ρ s v,
      stoppedProcess_eCauseSpecificHazard_eq_lintegral μ ρ t v]
    exact lintegral_mono_set (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst))
  have hmonoNat : Monotone (fun n : ℕ ↦ H (n : ℝ≥0)) := by
    intro n m hnm v
    exact hmono v (by exact_mod_cast hnm)
  have hmInf : Measurable Hinf := Measurable.iSup fun n : ℕ ↦ hm (n : ℝ≥0)
  have hmean : (∫⁻ v, Hinf v ∂μ) ≤ ρ univ := by
    change (∫⁻ v, ⨆ n : ℕ, H (n : ℝ≥0) v ∂μ) ≤ ρ univ
    rw [lintegral_iSup (fun n : ℕ ↦ hm (n : ℝ≥0)) hmonoNat]
    refine iSup_le fun n ↦ ?_
    change (∫⁻ v, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id (n : ℝ≥0) v ∂μ) ≤ ρ univ
    rw [lintegral_stoppedProcess_eCauseSpecificHazard μ ρ hρ (n : ℝ≥0)]
    exact measure_mono (subset_univ _)
  have hmeanFinite : (∫⁻ v, Hinf v ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top ρ univ) hmean
  have hfinite : ∀ᵐ v ∂μ, Hinf v < ∞ := ae_lt_top hmInf hmeanFinite
  have hi : Integrable (fun v ↦ (Hinf v).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hmInf.aemeasurable hmeanFinite
  have hu : UniformIntegrable (fun _ : ℝ≥0 ↦ fun v ↦ (Hinf v).toReal) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hi)
  apply hu.mono_norm
    (fun t ↦ (integrable_stoppedProcess_eCauseSpecificHazard μ ρ hρ t).1.aestronglyMeasurable)
  intro t
  obtain ⟨n, htn⟩ := exists_nat_ge t
  filter_upwards [hfinite] with v hv
  have htInf : H t v ≤ Hinf v :=
    (hmono v htn).trans (le_iSup (fun n : ℕ ↦ H (n : ℝ≥0) v) n)
  have htFinite : H t v ≠ ∞ := ne_top_of_le_ne_top hv.ne htInf
  have hreal : (H t v).toReal ≤ (Hinf v).toReal :=
    (ENNReal.toReal_le_toReal htFinite hv.ne).mpr htInf
  change ‖(H t v).toReal‖ ≤ ‖(Hinf v).toReal‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hreal

end ProbabilityTheory
