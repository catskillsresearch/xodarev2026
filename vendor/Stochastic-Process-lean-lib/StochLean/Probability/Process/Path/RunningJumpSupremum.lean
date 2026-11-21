/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightContinuousSupremum
public import StochLean.Probability.Process.Path.CadlagBounded
public import StochLean.Probability.Process.Path.JumpStopping
public import StochLean.Probability.Process.Stopping.JumpCoefficients

/-! # The actual running jump supremum and the factor-two bound

The jump supremum is taken over all times in the closed interval, not over a
dense grid that could miss isolated jumps. It includes the source initial
jump `X 0`. Compact cadlag boundedness makes both extended suprema finite.

The correct path bound is `J <= 2 X*`. The factor of two dropped on Protter's
printed p.132 is retained. No measurability of this uncountable supremum is
asserted here; that requires the actual jump-enumeration bridge separately.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- The actual positive norm supremum of the source jumps, including time
zero. It is extended-valued until path boundedness has been established. -/
noncomputable def eRunningJumpSupremum (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ‖jumpProcess X t ω‖

@[simp] theorem eRunningJumpSupremum_zero (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    eRunningJumpSupremum X 0 ω = ENNReal.ofReal ‖X 0 ω‖ := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    have ht0 : t = 0 := le_antisymm ht bot_le
    simp only [ht0, jumpProcess_zero, le_refl]
  · exact le_iSup_of_le 0 (le_iSup_of_le le_rfl (by rw [jumpProcess_zero]))

/-- Finite compact path bounds justify the real running norm supremum. -/
theorem IsCadlagPath.denseRunningSupremum_norm_ne_top
    (hX : IsCadlagPath (X · ω)) (T : ℝ≥0) :
    denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω ≠ ∞ := by
  obtain ⟨K, _, hK⟩ := hX.exists_norm_bound_Icc T
  exact denseRunningSupremum_ne_top_of_le (fun t ht ↦ hK t ⟨bot_le, ht⟩)

/-- The running jump norm can be twice the running path norm. The original
time-zero value is retained, and no maximum-attainment assertion is used. -/
theorem IsCadlagPath.eRunningJumpSupremum_le_two_mul
    (hX : IsCadlagPath (X · ω)) (T : ℝ≥0) :
    eRunningJumpSupremum X T ω ≤
      2 * denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω := by
  have hfin := hX.denseRunningSupremum_norm_ne_top T
  let K := (denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω).toReal
  have hn : IsRightContinuousPath (fun t ↦ ‖X t ω‖) :=
    fun t ↦ continuous_norm.continuousAt.comp_continuousWithinAt (hX.1 t)
  have hb : ∀ s, ‖X (min s T) ω‖ ≤ K :=
    fun s ↦ le_toReal_denseRunningSupremum_of_rightContinuous (min_le_right _ _) hn hfin
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hj := (hX.min_const T).norm_jumpProcess_le_of_bound hb t
  rw [hX.jumpProcess_min_const T t, if_pos ht] at hj
  calc
    ENNReal.ofReal ‖jumpProcess X t ω‖ ≤ ENNReal.ofReal (2 * K) :=
      ENNReal.ofReal_le_ofReal hj
    _ = 2 * denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat, K, ENNReal.ofReal_toReal hfin]

/-- The actual all-times jump supremum is finite on every compact cadlag path. -/
theorem IsCadlagPath.eRunningJumpSupremum_ne_top
    (hX : IsCadlagPath (X · ω)) (T : ℝ≥0) : eRunningJumpSupremum X T ω ≠ ∞ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) (hX.denseRunningSupremum_norm_ne_top T))
    (hX.eRunningJumpSupremum_le_two_mul T)

end ProbabilityTheory
