/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.JumpStopping
public import StochLean.Analysis.PathVariation.StoppedJumpSum

/-! # Stopping one factor in the positive-time mixed-jump series -/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.tsum_jump_mul_stoppedProcess (hX : IsCadlagPath (X · ω))
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    (∑' s : Ioc 0 t, jumpProcess (MeasureTheory.stoppedProcess X τ) s ω * jumpProcess Y s ω) =
      ∑' s : Ioc 0 ((min (t : WithTop ℝ≥0) (τ ω)).untopA),
        jumpProcess X s ω * jumpProcess Y s ω := by
  cases hτ : τ ω with
  | top =>
    simp only [WithTop.untopA]
    apply tsum_congr
    intro s
    rw [hX.jumpProcess_stoppedProcess τ s, hτ, if_pos le_top]
  | coe a =>
    simp only [← WithTop.coe_min, WithTop.untopD_coe]
    calc
      _ = ∑' s : Ioc 0 t,
          (if (s : ℝ≥0) ≤ a then jumpProcess X s ω * jumpProcess Y s ω else 0) := by
        apply tsum_congr
        intro s
        rw [hX.jumpProcess_stoppedProcess τ s, hτ]
        simp only [WithTop.coe_le_coe]
        split_ifs <;> simp only [zero_mul]
      _ = _ := tsum_Ioc_cutoff_le (fun s ↦ jumpProcess X s ω * jumpProcess Y s ω) a t

end ProbabilityTheory
