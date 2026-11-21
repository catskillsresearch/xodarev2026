/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LargeJumpSum
public import StochLean.Probability.Process.Path.FiniteVariation

/-! # The actual large-jump cumulative processes

These are the signed and norm sums of the original jumps strictly larger
than the threshold, over the actual positive-time interval. They do not
select a decomposition or depend on an enumeration. The deterministic
locally finite sum results give common-event cadlag/FV properties and the
exact jumps. Measurability and locally integrable variation are separate
later conclusions, not part of the definitions.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The actual signed sum of positive-time jumps strictly larger than b.
It has no time-zero atom, regardless of the original initial random value. -/
noncomputable def largeJumpSumProcess (X : ℝ≥0 → Ω → ℝ) (b : ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
  if b < ‖jumpProcess X s ω‖ then jumpProcess X s ω else 0

/-- The actual norm sum of positive-time jumps strictly larger than b.
This is not a second total-variation owner; it bounds the signed sum's
existing actual variation on every compact interval. -/
noncomputable def largeJumpNormSumProcess (X : ℝ≥0 → Ω → ℝ) (b : ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
  if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0

theorem largeJumpSumProcesses_initial (X : ℝ≥0 → Ω → ℝ) (b : ℝ) :
    largeJumpSumProcess X b 0 = 0 ∧ largeJumpNormSumProcess X b 0 = 0 :=
  ⟨funext fun ω ↦ (large_jump_sums_zero X b ω).1,
    funext fun ω ↦ (large_jump_sums_zero X b ω).2⟩

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- The two original cumulative processes retain common-event path properties,
and actual extended variation is bounded before any real conversion. -/
theorem HasCadlagPaths.largeJumpSumProcesses_properties (hc : HasCadlagPaths X P)
    (hb : 0 < b) :
    HasCadlagPaths (largeJumpSumProcess X b) P ∧
      HasCadlagPaths (largeJumpNormSumProcess X b) P ∧
      HasFiniteVariationPaths (largeJumpSumProcess X b) P ∧
      HasMonotonePaths (largeJumpNormSumProcess X b) P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ largeJumpNormSumProcess X b t ω) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        eVariationOn (largeJumpSumProcess X b · ω) (Icc 0 T) ≤
          ENNReal.ofReal (largeJumpNormSumProcess X b T ω)) := by
  have hm : HasMonotonePaths (largeJumpNormSumProcess X b) P :=
    hc.mono fun _ hω ↦ hω.monotone_abs_large_jump_sum hb
  refine ⟨hc.mono (fun _ hω ↦ (hω.cadlag_large_jump_sums hb).1),
    hc.mono (fun _ hω ↦ (hω.cadlag_large_jump_sums hb).2),
    hc.mono (fun _ hω ↦ hω.locallyBoundedVariationOn_large_jump_sum hb),
    hm, ?_, hc.mono (fun _ hω ↦ hω.eVariationOn_large_jump_sum_le hb)⟩
  filter_upwards [hm] with ω hω t
  have h := hω (bot_le : (0 : ℝ≥0) ≤ t)
  change largeJumpNormSumProcess X b 0 ω ≤ largeJumpNormSumProcess X b t ω at h
  simpa only [(largeJumpSumProcesses_initial X b).2, Pi.zero_apply] using h

/-- The two processes retain exactly the large jump and its norm. The
source's separate time-zero jump convention is unchanged. -/
theorem HasCadlagPaths.jump_largeJumpSumProcesses (hc : HasCadlagPaths X P)
    (hb : 0 < b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      jumpProcess (largeJumpSumProcess X b) t ω =
        (if b < ‖jumpProcess X t ω‖ then jumpProcess X t ω else 0) ∧
      jumpProcess (largeJumpNormSumProcess X b) t ω =
        (if b < ‖jumpProcess X t ω‖ then ‖jumpProcess X t ω‖ else 0) := by
  filter_upwards [hc] with ω hω t ht
  simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne',
    largeJumpSumProcess, largeJumpNormSumProcess] using hω.large_jump_sums_sub_leftLim hb ht

/-- After removing the actual large-jump sum, every positive-time jump has
norm at most b, including jumps whose norm is exactly b. -/
theorem HasCadlagPaths.norm_jump_sub_largeJumpSumProcess_le (hc : HasCadlagPaths X P)
    (hb : 0 < b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess (X - largeJumpSumProcess X b) t ω‖ ≤ b :=
  hc.mono fun _ hω _ ht ↦ hω.norm_jump_residual_large_jump_sum_le hb ht

/-- Common path equality preserves the actual sums independently of any
enumeration, threshold positivity, or measurability of the input processes. -/
theorem Indistinguishable.largeJumpSumProcesses (he : Indistinguishable X Y P) (b : ℝ) :
    Indistinguishable (largeJumpSumProcess X b) (largeJumpSumProcess Y b) P ∧
      Indistinguishable (largeJumpNormSumProcess X b) (largeJumpNormSumProcess Y b) P := by
  constructor <;> filter_upwards [he.jumpProcess] with ω hω t
  · simp only [largeJumpSumProcess, hω]
  · simp only [largeJumpNormSumProcess, hω]

end ProbabilityTheory
