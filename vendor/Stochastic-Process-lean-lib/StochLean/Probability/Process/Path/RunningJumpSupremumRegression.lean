/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RunningJumpSupremum
public import StochLean.Probability.Process.Path.LifetimeStepJump

/-! # The factor two in the running-jump bound is necessary

A cadlag path changing from one to minus one has running path norm one and
running jump norm two. This directly rejects the dropped factor on Protter's
printed p.132, rather than merely asserting the corrected upper bound.
-/

@[expose] public section

open ProbabilityTheory
open scoped NNReal ENNReal

namespace StochLean.SemimartingaleRegression

/-- A genuine cadlag counterexample to the factor-one running-jump bound. -/
theorem running_jump_supremum_requires_factor_two :
    ∃ X : ℝ≥0 → Unit → ℝ,
      IsCadlagPath (X · ()) ∧
      denseRunningSupremum (fun t ω ↦ ‖X t ω‖) 1 () = 1 ∧
      eRunningJumpSupremum X 1 () = 2 ∧
      ¬ eRunningJumpSupremum X 1 () ≤
        denseRunningSupremum (fun t ω ↦ ‖X t ω‖) 1 () := by
  let C : ℝ≥0 → Unit → ℝ := fun _ _ ↦ 1
  let S : ℝ≥0 → Unit → ℝ := fun t _ ↦ if (1 : ℝ≥0) ≤ t then 2 else 0
  let X := C - S
  have hC : IsCadlagPath (C · ()) := IsContinuousPath.isCadlagPath continuous_const
  have hS : IsCadlagPath (S · ()) := isCadlagPath_step_Ici 1 (2 : ℝ)
  have hX : IsCadlagPath (X · ()) := hC.sub hS
  have hn (t : ℝ≥0) : ‖X t ()‖ = 1 := by
    by_cases ht : (1 : ℝ≥0) ≤ t <;> norm_num [X, C, S, Pi.sub_apply, ht]
  have hs : denseRunningSupremum (fun t ω ↦ ‖X t ω‖) 1 () = 1 := by
    simp only [denseRunningSupremum, hn, ENNReal.ofReal_one, iSup_const]
  have hj : jumpProcess X 1 () = -2 := by
    change jumpProcess (C - S) 1 () = -2
    rw [hC.jumpProcess_sub hS]
    have hc : IsContinuousPath (C · ()) := continuous_const
    rw [hc.jumpProcess_eq_zero (by norm_num)]
    change 0 - jumpProcess (fun t (_ : Unit) ↦ if (1 : ℝ≥0) ≤ t then (2 : ℝ) else 0)
      1 () = -2
    rw [jumpProcess_step_Ici]
    norm_num
  have he : eRunningJumpSupremum X 1 () = 2 := by
    apply le_antisymm
    · simpa only [hs, mul_one] using hX.eRunningJumpSupremum_le_two_mul 1
    · calc
        (2 : ℝ≥0∞) = ENNReal.ofReal ‖jumpProcess X 1 ()‖ := by rw [hj]; norm_num
        _ ≤ eRunningJumpSupremum X 1 () :=
          le_iSup_of_le 1 (le_iSup_of_le le_rfl le_rfl)
  refine ⟨X, hX, hs, he, ?_⟩
  rw [he, hs]
  norm_num

end StochLean.SemimartingaleRegression
