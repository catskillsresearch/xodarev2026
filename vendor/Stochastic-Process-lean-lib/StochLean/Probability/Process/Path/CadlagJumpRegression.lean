/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.FiniteJumpRemoval
public import StochLean.Probability.Process.Path.CadlagWindowOscillation
public import StochLean.Probability.Process.Stopping.LargeJumpTimes
public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps

/-! # Regressions for positive-time jump enumeration and removal -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochLean.SemimartingaleRegression

/-- Positive-time jump classification imposes no initial-value or integrability condition. -/
theorem inaccessible_jumps_allow_arbitrary_initial_constant
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (C : Ω → ℝ) :
    HasTotallyInaccessibleJumps F (fun _ ω ↦ C ω) P ∧
      jumpProcess (fun _ ω ↦ C ω) 0 = C := by
  have hc : HasContinuousPaths (fun _ : ℝ≥0 ↦ C) P :=
    Eventually.of_forall fun _ ↦ continuous_const
  exact ⟨hc.hasTotallyInaccessibleJumps F, jumpProcess_zero _⟩

/-- A constant path has no next positive-time jump, even when its initial value is large. -/
theorem next_large_jump_constant_is_infinite {Ω : Type*} (C : Ω → ℝ)
    (σ : Ω → WithTop ℝ≥0) {b : ℝ} (hb : 0 < b) (ω : Ω) :
    nextLargeJump (fun _ ω ↦ C ω) b σ ω = ⊤ := by
  apply nextLargeJump_eq_top_iff.mpr
  rintro t ⟨hst, hj⟩
  have ht : 0 < t := WithTop.coe_lt_coe.mp
    ((show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ σ ω from bot_le).trans_lt hst)
  have hc : IsContinuousPath (fun _ : ℝ≥0 ↦ C ω) := continuous_const
  rw [hc.jumpProcess_eq_zero (ne_of_gt ht), norm_zero] at hj
  exact (not_lt_of_ge hb.le) hj

/-- Removing the same jump twice over-cancels it. Uniqueness of selected finite
lifetimes in the cancellation theorem is a real mathematical condition. -/
theorem repeated_finite_jump_removal_overcancels :
    jumpProcess (fun (t : ℝ≥0) (_ : Unit) ↦
      (if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0) -
        ((if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0) +
          (if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0))) 1 () = -1 := by
  have he : (fun (t : ℝ≥0) (_ : Unit) ↦
      (if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0) -
        ((if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0) +
          (if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0))) =
      (fun (t : ℝ≥0) (_ : Unit) ↦ if (1 : ℝ≥0) ≤ t then (-1 : ℝ) else 0) := by
    funext t _
    split_ifs <;> norm_num
  rw [he, jumpProcess_step_Ici]
  simp only [if_true]

/-- The jump process of a cadlag step is not right-continuous. Its first jump
cannot be justified by applying right-continuous hitting to the jump process. -/
theorem cadlag_step_jump_process_not_right_continuous :
    ¬ IsRightContinuousPath (fun t : ℝ≥0 ↦
      jumpProcess (fun (s : ℝ≥0) (_ : Unit) ↦
        if (1 : ℝ≥0) ≤ s then (1 : ℝ) else 0) t ()) := by
  intro hr
  let d : ℕ → ℝ≥0 := fun n ↦ 1 / ((n : ℝ≥0) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdpos (n) : 0 < d n := by dsimp [d]; positivity
  have hseq : Tendsto (fun n ↦ (1 : ℝ≥0) + d n) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hw : Tendsto (fun n ↦ (1 : ℝ≥0) + d n) atTop (𝓝[≥] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hseq, Eventually.of_forall fun n ↦
      le_add_of_nonneg_right (hdpos n).le⟩
  have hlim := (hr 1).tendsto.comp hw
  simp only [Function.comp_def, jumpProcess_step_Ici, if_true] at hlim
  have hz (n) : (if (1 : ℝ≥0) = 1 + d n then (1 : ℝ) else 0) = 0 := by
    exact if_neg (ne_of_lt (lt_add_of_pos_right 1 (hdpos n)))
  simp only [hz] at hlim
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact zero_ne_one he

end StochLean.SemimartingaleRegression
