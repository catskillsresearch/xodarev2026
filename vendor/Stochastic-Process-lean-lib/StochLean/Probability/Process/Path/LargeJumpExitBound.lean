/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LargeJumpSum
public import StochLean.Probability.Process.Stopping.CadlagExitLocalization

/-! # Actual large-jump variation at a joint norm exit

Write `C` for the actual cumulative norm of the large positive-time jumps.
The existing capped norm exits of `C + norm X` bound both summands strictly
before exit. Their genuine left limits retain those bounds at the exit,
and the exact jump of `C` is at most the norm of the jump of `X`.

The resulting bound retains the actual possibly overshooting value of `X`.
It does not assert that the stopped original process is bounded. The case
of an exit at zero uses `C 0 = 0` and needs no initial-value hypothesis on
`X`. All exit samples are explicitly known finite before `untopA` is used.
No filtration, measurability, moment, or martingale premise is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

/-- Up to and including the actual joint exit, the cumulative large-jump
norm is controlled by the exit level and the current original value.
The endpoint may overshoot; its original value is retained on the right. -/
theorem IsCadlagPath.largeJumpNormSumProcess_le_before_joint_exit
    (hx : IsCadlagPath (X · ω)) (hb : 0 < b) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ cappedNormExitSequence
      (fun s v ↦ largeJumpNormSumProcess X b s v + ‖X s v‖) n ω) :
    largeJumpNormSumProcess X b t ω ≤ 2 * ((n + 1 : ℕ) : ℝ) + ‖X t ω‖ := by
  let C := largeJumpNormSumProcess X b
  let Z : ℝ≥0 → Ω → ℝ := fun s v ↦ C s v + ‖X s v‖
  have hc : IsCadlagPath (C · ω) := (hx.cadlag_large_jump_sums hb).2
  have hm : Monotone (C · ω) := hx.monotone_abs_large_jump_sum hb
  have hC0 : C 0 ω = 0 := congrFun (largeJumpSumProcesses_initial X b).2 ω
  have hnC (s : ℝ≥0) : 0 ≤ C s ω := by
    have h := hm (bot_le : (0 : ℝ≥0) ≤ s)
    change C 0 ω ≤ C s ω at h
    rwa [hC0] at h
  by_cases hz : t = 0
  · subst t
    change C 0 ω ≤ _
    rw [hC0]
    positivity
  have hp : 0 < t := pos_iff_ne_zero.mpr hz
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hp⟩
  have hpre (s : ℝ≥0) (hs : s < t) :
      C s ω ≤ ((n + 1 : ℕ) : ℝ) ∧ ‖X s ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
    have hclock : (s : WithTop ℝ≥0) < cappedNormExitSequence Z n ω :=
      (WithTop.coe_lt_coe.mpr hs).trans_le ht
    have hbound := norm_le_of_lt_cappedNormExitSequence hclock
    change ‖C s ω + ‖X s ω‖‖ ≤ ((n + 1 : ℕ) : ℝ) at hbound
    rw [Real.norm_of_nonneg (add_nonneg (hnC s) (norm_nonneg _))] at hbound
    constructor <;> linarith only [hbound, hnC s, norm_nonneg (X s ω)]
  have hlC : leftLimitProcess C t ω ≤ ((n + 1 : ℕ) : ℝ) := by
    apply le_of_tendsto (hc.tendsto_leftLimitProcess hz)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hpre s hs).1
  have hlX : ‖leftLimitProcess X t ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
    apply le_of_tendsto (hx.tendsto_leftLimitProcess hz).norm
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hpre s hs).2
  have hjC : jumpProcess C t ω =
      if b < ‖jumpProcess X t ω‖ then ‖jumpProcess X t ω‖ else 0 := by
    change C t ω - leftLimitProcess C t ω = _
    rw [leftLimitProcess, if_neg hz]
    exact (hx.large_jump_sums_sub_leftLim hb hp).2
  have hjle : jumpProcess C t ω ≤ ‖jumpProcess X t ω‖ := by
    rw [hjC]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hjX : ‖jumpProcess X t ω‖ ≤ ‖X t ω‖ + ‖leftLimitProcess X t ω‖ :=
    norm_sub_le _ _
  have heC : C t ω = jumpProcess C t ω + leftLimitProcess C t ω :=
    (sub_add_cancel _ _).symm
  change C t ω ≤ _
  linarith only [hlC, hlX, hjle, hjX, heC]

/-- The entire stopped cumulative norm process is dominated by the actual
original exit sample plus twice the level. The cap proves this sample is
finite, including when the exit is zero. -/
theorem IsCadlagPath.largeJumpNormSumProcess_stopped_joint_exit_le
    (hx : IsCadlagPath (X · ω)) (hb : 0 < b) (n : ℕ) (t : ℝ≥0) :
    stoppedProcess (largeJumpNormSumProcess X b)
      (cappedNormExitSequence (fun s v ↦ largeJumpNormSumProcess X b s v + ‖X s v‖) n)
      t ω ≤ 2 * ((n + 1 : ℕ) : ℝ) +
        ‖X ((cappedNormExitSequence
          (fun s v ↦ largeJumpNormSumProcess X b s v + ‖X s v‖) n ω).untopA) ω‖ := by
  let C := largeJumpNormSumProcess X b
  let Z : ℝ≥0 → Ω → ℝ := fun s v ↦ C s v + ‖X s v‖
  let ρ := cappedNormExitSequence Z n
  let r : ℝ≥0 := (ρ ω).untopA
  have hfin : ρ ω ≠ ⊤ := cappedNormExitSequence_ne_top Z n ω
  have hr : (r : WithTop ℝ≥0) = ρ ω := by
    dsimp only [r]
    rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
  have hclock : (min (t : WithTop ℝ≥0) (ρ ω)).untopA ≤ r := by
    apply WithTop.untopA_le
    rw [hr]
    exact min_le_right _ _
  have hbR : C r ω ≤ 2 * ((n + 1 : ℕ) : ℝ) + ‖X r ω‖ :=
    hx.largeJumpNormSumProcess_le_before_joint_exit hb hr.le
  change C ((min (t : WithTop ℝ≥0) (ρ ω)).untopA) ω ≤ _
  exact (hx.monotone_abs_large_jump_sum hb hclock).trans hbR

end ProbabilityTheory
