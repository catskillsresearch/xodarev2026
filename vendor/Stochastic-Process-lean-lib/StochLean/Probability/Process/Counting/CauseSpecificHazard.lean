/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardBalance

/-! # Cause-specific cumulative hazard for an actual observation submeasure

The observation law supplies the pre-jump survival denominator, while its
cause submeasure supplies the integration measure. Thus competing causes
share the actual at-risk survival. No independence or normalized conditional
law is used. Initial and infinite atoms do not contribute finite positive
jumps. The ordinary cumulative hazard is recovered exactly when the cause
submeasure is the whole observation law.

The definition remains ENNReal. Domination by the observation law bounds
it by the existing ordinary hazard, so a positive-survival cap proves
finiteness before any real-valued use. This is a distinct cause-specific
integral, not another compensator or a replacement ordinary hazard owner.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- The hazard of a cause submeasure, using the observation law's closed
survival denominator. Applications establish the actual domination `ρ ≤ μ`. -/
noncomputable def eCauseSpecificHazard
    (μ ρ : Measure (WithTop ℝ≥0)) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), (μ (Ici u))⁻¹ ∂ρ

variable (μ ρ : Measure (WithTop ℝ≥0))

/-- Selecting all causes recovers the sole ordinary cumulative hazard. -/
theorem eCauseSpecificHazard_self (t : ℝ≥0) :
    eCauseSpecificHazard μ μ t = eCumulativeHazard μ t := rfl

theorem eCauseSpecificHazard_zero : eCauseSpecificHazard μ ρ 0 = 0 := by
  simp only [eCauseSpecificHazard, WithTop.coe_zero, Ioc_self,
    Measure.restrict_empty, lintegral_zero_measure]

theorem monotone_eCauseSpecificHazard : Monotone (eCauseSpecificHazard μ ρ) := by
  intro s t hst
  exact lintegral_mono_set (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst))

theorem measurable_eCauseSpecificHazard : Measurable (eCauseSpecificHazard μ ρ) :=
  (monotone_eCauseSpecificHazard μ ρ).measurable

/-- A genuine cause submeasure has no larger hazard than all causes together. -/
theorem eCauseSpecificHazard_le_eCumulativeHazard
    (hρ : ρ ≤ μ) (t : ℝ≥0) :
    eCauseSpecificHazard μ ρ t ≤ eCumulativeHazard μ t := by
  exact lintegral_mono' (Measure.restrict_mono_measure hρ _) le_rfl

/-- An actual positive-survival cap makes the extended cause hazard finite. -/
theorem eCauseSpecificHazard_ne_top_of_le [IsFiniteMeasure μ]
    (hρ : ρ ≤ μ) {t T : ℝ≥0}
    (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) (ht : t ≤ T) :
    eCauseSpecificHazard μ ρ t ≠ ∞ :=
  ne_top_of_le_ne_top (eCumulativeHazard_ne_top_of_le μ hT ht)
    (eCauseSpecificHazard_le_eCumulativeHazard μ ρ hρ t)

/-- Stopping at the observation lifetime retains precisely the cause times
at or before that lifetime. The stopped clock is finite even at infinity. -/
theorem stoppedProcess_eCauseSpecificHazard_eq_lintegral
    (t : ℝ≥0) (v : WithTop ℝ≥0) :
    stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id t v =
      ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0),
        (Iic v).indicator (fun u ↦ (μ (Ici u))⁻¹) u ∂ρ := by
  classical
  have hfin : min (t : WithTop ℝ≥0) v ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hclock : (((min (t : WithTop ℝ≥0) v).untopA : ℝ≥0) : WithTop ℝ≥0) =
      min (t : WithTop ℝ≥0) v := by
    rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
  change eCauseSpecificHazard μ ρ (min (t : WithTop ℝ≥0) v).untopA = _
  rw [eCauseSpecificHazard, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hclock]
  have hs : Ioc (0 : WithTop ℝ≥0) (min (t : WithTop ℝ≥0) v) =
      Iic v ∩ Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    ext u
    simp only [mem_Ioc, mem_inter_iff, mem_Iic, le_min_iff]
    exact ⟨fun h ↦ ⟨h.2.2, h.1, h.2.1⟩, fun h ↦ ⟨h.2.1, h.2.2, h.1⟩⟩
  rw [hs]

end ProbabilityTheory
