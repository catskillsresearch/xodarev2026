/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RunningJumpSupremum

/-! # Stopping the actual running jump supremum

The existing all-times jump supremum commutes with closed stopping on each
cadlag path. A finite stopping endpoint retains its jump, lifetime zero
retains the initial jump, and infinite lifetime changes no finite value.
An independent sample-event restriction also commutes exactly.

Together these identities give the real-valued native masked stopping
formula without introducing a new supremum or lifetime selector. The
equalities themselves are pathwise: no stopping-time or measurability
assumptions are needed. Compact finiteness of the cadlag jump supremum is
available from the imported owner when using the real value as a bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- Closed stopping commutes with the actual extended running jump supremum.
The endpoint and initial jumps are included, also when the lifetime is zero. -/
theorem IsCadlagPath.eRunningJumpSupremum_stoppedProcess
    (hX : IsCadlagPath (X · ω)) (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) :
    eRunningJumpSupremum (MeasureTheory.stoppedProcess X τ) T ω =
      MeasureTheory.stoppedProcess (eRunningJumpSupremum X) τ T ω := by
  change eRunningJumpSupremum (MeasureTheory.stoppedProcess X τ) T ω =
    eRunningJumpSupremum X ((min (T : WithTop ℝ≥0) (τ ω)).untopA) ω
  cases hτ : τ ω with
  | top =>
    simp only [min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
    apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    rw [hX.jumpProcess_stoppedProcess τ t, hτ, if_pos le_top]
  | coe a =>
    simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
    apply le_antisymm
    · apply iSup_le
      intro t
      apply iSup_le
      intro ht
      rw [hX.jumpProcess_stoppedProcess τ t, hτ]
      simp only [WithTop.coe_le_coe]
      by_cases ha : t ≤ a
      · rw [if_pos ha]
        exact le_iSup_of_le t (le_iSup_of_le (le_min ht ha) le_rfl)
      · simp only [if_neg ha, norm_zero, ENNReal.ofReal_zero, zero_le]
    · apply iSup_le
      intro t
      apply iSup_le
      intro ht
      have htT : t ≤ T := ht.trans (min_le_left _ _)
      have hta : t ≤ a := ht.trans (min_le_right _ _)
      have he := hX.jumpProcess_stoppedProcess τ t
      rw [hτ] at he
      simp only [WithTop.coe_le_coe, if_pos hta] at he
      rw [← he]
      exact le_iSup_of_le t (le_iSup_of_le htT le_rfl)

/-- A fixed sample-event restriction commutes with the actual running jump
supremum, without measurability or path regularity assumptions. -/
theorem eRunningJumpSupremum_indicator (X : ℝ≥0 → Ω → ℝ) (E : Set Ω) :
    eRunningJumpSupremum (fun t ↦ E.indicator (X t)) =
      fun t ↦ E.indicator (eRunningJumpSupremum X t) := by
  classical
  funext T ω
  by_cases hE : ω ∈ E
  · simp only [eRunningJumpSupremum, indicator_of_mem hE, jumpProcess,
      Pi.sub_apply, leftLimitProcess]
  · rw [indicator_of_notMem hE]
    have hj (t : ℝ≥0) : jumpProcess (fun u ↦ E.indicator (X u)) t ω = 0 := by
      simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, indicator_of_notMem hE]
      rw [(continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))).continuousWithinAt.leftLim_eq]
      simp only [ite_self, sub_self]
    simp only [eRunningJumpSupremum, hj, norm_zero, ENNReal.ofReal_zero]
    exact le_antisymm (iSup_le fun _ ↦ iSup_le fun _ ↦ le_rfl) bot_le

/-- The real running jump supremum commutes with native masked stopping.
Only the mask removes the initial jump at a zero lifetime; infinity is not
converted into a sample time of the original process. -/
theorem IsCadlagPath.eRunningJumpSupremum_toReal_masked_stoppedProcess
    (hX : IsCadlagPath (X · ω)) (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) :
    (eRunningJumpSupremum (MeasureTheory.stoppedProcess
      (fun t ↦ {v | 0 < τ v}.indicator (X t)) τ) T ω).toReal =
      MeasureTheory.stoppedProcess (fun t ↦ {v | 0 < τ v}.indicator
        (fun v ↦ (eRunningJumpSupremum X t v).toReal)) τ T ω := by
  have hm : IsCadlagPath (fun t ↦ {v | 0 < τ v}.indicator (X t) ω) := by
    by_cases hp : ω ∈ {v | 0 < τ v}
    · simpa only [indicator_of_mem hp] using hX
    · simp only [indicator_of_notMem hp]
      exact IsContinuousPath.isCadlagPath continuous_const
  rw [hm.eRunningJumpSupremum_stoppedProcess τ T, eRunningJumpSupremum_indicator]
  by_cases hp : ω ∈ {v | 0 < τ v}
  · simp only [MeasureTheory.stoppedProcess, indicator_of_mem hp]
  · simp only [MeasureTheory.stoppedProcess, indicator_of_notMem hp, ENNReal.toReal_zero]

end ProbabilityTheory
