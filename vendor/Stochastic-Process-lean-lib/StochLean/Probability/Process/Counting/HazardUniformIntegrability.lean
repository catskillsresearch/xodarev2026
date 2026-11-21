/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardUnrestrictedMartingale
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # Global uniform integrability of the compensated closed count

The integer-time supremum of the actual extended stopped hazard has mean at
most one, by monotone convergence and the unrestricted stopped-hazard mean.
It is therefore finite almost surely and its real value is integrable.
This gives a single integrable envelope for the compensated count at every
finite time. No finite support endpoint, survival guard, or initial-atom
exclusion is needed. The supremum is only a local proof expression, not a
second hazard or terminal-value owner.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- The actual uncapped compensated closed count is uniformly integrable over
the whole halfline for every probability law of the extended lifetime. -/
theorem uniformIntegrable_singleJump_sub_hazard_unrestricted
    (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ] :
    UniformIntegrable (fun (t : ℝ≥0) (v : WithTop ℝ≥0) ↦
      (if v ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v)
      1 μ := by
  classical
  let H : ℝ≥0 → WithTop ℝ≥0 → ℝ≥0∞ :=
    stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id
  let Hinf : WithTop ℝ≥0 → ℝ≥0∞ := fun v ↦ ⨆ n : ℕ, H (n : ℝ≥0) v
  have hm (t : ℝ≥0) : Measurable (H t) :=
    (measurable_eCumulativeHazard μ).comp
      ((measurable_const.min measurable_id).untopA)
  have hmono (v : WithTop ℝ≥0) : Monotone (fun t : ℝ≥0 ↦ H t v) := by
    intro s t hst
    change stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id s v ≤
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v
    rw [stoppedProcess_eCumulativeHazard_eq_lintegral μ s v,
      stoppedProcess_eCumulativeHazard_eq_lintegral μ t v]
    exact lintegral_mono_set (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst))
  have hmonoNat : Monotone (fun n : ℕ ↦ H (n : ℝ≥0)) := by
    intro n m hnm v
    exact hmono v (by exact_mod_cast hnm)
  have hmInf : Measurable Hinf := Measurable.iSup fun n : ℕ ↦ hm (n : ℝ≥0)
  have hmean : (∫⁻ v, Hinf v ∂μ) ≤ 1 := by
    change (∫⁻ v, ⨆ n : ℕ, H (n : ℝ≥0) v ∂μ) ≤ 1
    rw [lintegral_iSup (fun n : ℕ ↦ hm (n : ℝ≥0)) hmonoNat]
    refine iSup_le fun n ↦ ?_
    change (∫⁻ v, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id (n : ℝ≥0) v ∂μ) ≤ 1
    rw [lintegral_stoppedProcess_eCumulativeHazard_unrestricted μ (n : ℝ≥0)]
    exact prob_le_one
  have hmeanFinite : (∫⁻ v, Hinf v ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hmean
  have hfinite : ∀ᵐ v ∂μ, Hinf v < ∞ := ae_lt_top hmInf hmeanFinite
  have hi : Integrable (fun v ↦ (Hinf v).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hmInf.aemeasurable hmeanFinite
  let G : WithTop ℝ≥0 → ℝ := fun v ↦ 1 + (Hinf v).toReal
  have hiG : Integrable G μ := (integrable_const (1 : ℝ)).add hi
  have hu : UniformIntegrable (fun _ : ℝ≥0 ↦ G) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hiG)
  apply hu.mono_norm
    (fun t ↦ ((martingale_singleJump_sub_hazard_unrestricted μ).integrable t).aestronglyMeasurable)
  intro t
  obtain ⟨n, htn⟩ := exists_nat_ge t
  filter_upwards [hfinite] with v hv
  have htInf : H t v ≤ Hinf v :=
    (hmono v htn).trans (le_iSup (fun n : ℕ ↦ H (n : ℝ≥0) v) n)
  have htFinite : H t v ≠ ∞ := ne_top_of_le_ne_top hv.ne htInf
  have hreal : (H t v).toReal ≤ (Hinf v).toReal :=
    (ENNReal.toReal_le_toReal htFinite hv.ne).mpr htInf
  have hcount : ‖if v ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0‖ ≤ 1 := by
    split_ifs <;> norm_num
  change ‖(if v ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) - (H t v).toReal‖ ≤ ‖G v‖
  apply (norm_sub_le _ _).trans
  have hnorm : ‖(H t v).toReal‖ ≤ (Hinf v).toReal := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hreal
  exact (add_le_add hcount hnorm).trans (le_abs_self (G v))

end ProbabilityTheory
