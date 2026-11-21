/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimitStopping
public import Mathlib.Probability.Process.Stopping

/-! # Source jumps of stopped cadlag paths

The endpoint jump is included: the cutoff is `t <= tau`, not `t < tau`.
The original initial jump is retained, including when the stopping time is zero.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.jumpProcess_min_const (hX : IsCadlagPath (X · ω)) (a t : ℝ≥0) :
    jumpProcess (fun u v ↦ X (min u a) v) t ω =
      if t ≤ a then jumpProcess X t ω else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [jumpProcess_zero, if_pos (show (0 : ℝ≥0) ≤ a from bot_le),
      min_eq_left (show (0 : ℝ≥0) ≤ a from bot_le)]
  · have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    have hl : leftLimitProcess (fun u v ↦ X (min u a) v) t ω =
        if a < t then X a ω else leftLimitProcess X t ω := by
      rw [leftLimitProcess, if_neg ht]
      apply leftLim_eq_of_tendsto
      simpa only [min_comm] using hX.tendsto_min_const_nhdsLT ht a
    change X (min t a) ω - leftLimitProcess (fun u v ↦ X (min u a) v) t ω = _
    rw [hl]
    by_cases ha : a < t
    · simp only [if_pos ha, min_eq_right ha.le, sub_self, if_neg (not_le_of_gt ha)]
    · simp only [if_neg ha, min_eq_left (le_of_not_gt ha), if_pos (le_of_not_gt ha)]
      rfl

theorem IsCadlagPath.jumpProcess_stoppedProcess (hX : IsCadlagPath (X · ω))
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    jumpProcess (MeasureTheory.stoppedProcess X τ) t ω =
      if (t : WithTop ℝ≥0) ≤ τ ω then jumpProcess X t ω else 0 := by
  cases hτ : τ ω with
  | top =>
    simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, MeasureTheory.stoppedProcess,
      hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, if_pos le_top]
  | coe a =>
    simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, MeasureTheory.stoppedProcess,
      hτ, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, WithTop.coe_le_coe]
      using hX.jumpProcess_min_const a t

end ProbabilityTheory
