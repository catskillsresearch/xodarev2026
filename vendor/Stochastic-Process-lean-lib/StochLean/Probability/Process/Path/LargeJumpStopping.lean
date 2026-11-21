/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LargeJumpSum
public import StochLean.Probability.Process.Path.JumpStopping
public import StochLean.Analysis.PathVariation.StoppedJumpSum

/-! # Stopping and event restriction of the actual large-jump sums

Both cumulative processes commute with stopping on the common cadlag event.
The lifetime need not be a stopping time: this is a path identity. The jump
at a finite stopping endpoint is included, while an infinite lifetime leaves
every finite-time value unchanged. At lifetime zero both cumulative sums
are zero, because their actual index interval excludes the initial atom.

Restriction to a fixed sample event commutes exactly, without measurability
or path regularity assumptions. All four identities hold for an arbitrary
real threshold: each of the two truncation maps sends zero to zero. No
global absolute summability, infinite-time value, or new process selector
is introduced.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

private theorem tsum_jump_transform_stoppedProcess (hx : IsCadlagPath (X · ω))
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    (∑' s : Ioc 0 t, φ (jumpProcess (MeasureTheory.stoppedProcess X τ) s ω)) =
      ∑' s : Ioc 0 ((min (t : WithTop ℝ≥0) (τ ω)).untopA), φ (jumpProcess X s ω) := by
  cases hτ : τ ω with
  | top =>
    simp only [WithTop.untopA]
    apply tsum_congr
    intro s
    rw [hx.jumpProcess_stoppedProcess τ s, hτ, if_pos le_top]
  | coe a =>
    simp only [← WithTop.coe_min, WithTop.untopD_coe]
    calc
      _ = ∑' s : Ioc 0 t,
          if (s : ℝ≥0) ≤ a then φ (jumpProcess X s ω) else 0 := by
        apply tsum_congr
        intro s
        rw [hx.jumpProcess_stoppedProcess τ s, hτ]
        simp only [WithTop.coe_le_coe]
        split_ifs <;> simp only [hφ]
      _ = _ := tsum_Ioc_cutoff_le (fun s ↦ φ (jumpProcess X s ω)) a t

private theorem tsum_jump_transform_indicator (X : ℝ≥0 → Ω → ℝ)
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) (S : Set Ω) :
    (fun (t : ℝ≥0) ω ↦ ∑' s : Ioc 0 t,
      φ (jumpProcess (fun u ↦ S.indicator (X u)) s ω)) =
      fun t ↦ S.indicator (fun ω ↦ ∑' s : Ioc 0 t, φ (jumpProcess X s ω)) := by
  classical
  funext t ω
  by_cases hS : ω ∈ S
  · simp only [indicator_of_mem hS, jumpProcess, Pi.sub_apply, leftLimitProcess]
  · rw [indicator_of_notMem hS]
    have hj (s : ℝ≥0) : jumpProcess (fun u ↦ S.indicator (X u)) s ω = 0 := by
      simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, indicator_of_notMem hS]
      rw [(continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))).continuousWithinAt.leftLim_eq]
      simp only [ite_self, sub_self]
    simp only [hj, hφ, tsum_zero]

/-- The signed cumulative large jumps commute exactly with restriction to
an arbitrary sample event. Neither measurability nor cadlag paths are needed. -/
theorem largeJumpSumProcess_indicator (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (S : Set Ω) :
    largeJumpSumProcess (fun t ↦ S.indicator (X t)) b =
      fun t ↦ S.indicator (largeJumpSumProcess X b t) :=
  tsum_jump_transform_indicator X (fun z ↦ if b < ‖z‖ then z else 0)
    (by simp only [ite_self]) S

/-- The absolute cumulative large jumps also commute exactly with event
restriction; an event outside the sample contributes no positive-time jump. -/
theorem largeJumpNormSumProcess_indicator (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (S : Set Ω) :
    largeJumpNormSumProcess (fun t ↦ S.indicator (X t)) b =
      fun t ↦ S.indicator (largeJumpNormSumProcess X b t) :=
  tsum_jump_transform_indicator X (fun z ↦ if b < ‖z‖ then ‖z‖ else 0)
    (by simp only [norm_zero, ite_self]) S

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Closed stopping retains its endpoint jump in the actual signed sum.
The lifetime is arbitrary, including zero and infinity; its measurability
is not a premise for this common pathwise identity. -/
theorem HasCadlagPaths.largeJumpSumProcess_stoppedProcess (hc : HasCadlagPaths X P)
    (b : ℝ) (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (largeJumpSumProcess (MeasureTheory.stoppedProcess X τ) b)
      (MeasureTheory.stoppedProcess (largeJumpSumProcess X b) τ) P := by
  filter_upwards [hc] with ω hω t
  exact tsum_jump_transform_stoppedProcess hω (fun z ↦ if b < ‖z‖ then z else 0)
    (by simp only [ite_self]) τ t

/-- The actual norm sum has the same closed stopping identity, with no
whole-half-line summability or value of the original process at infinity. -/
theorem HasCadlagPaths.largeJumpNormSumProcess_stoppedProcess (hc : HasCadlagPaths X P)
    (b : ℝ) (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (largeJumpNormSumProcess (MeasureTheory.stoppedProcess X τ) b)
      (MeasureTheory.stoppedProcess (largeJumpNormSumProcess X b) τ) P := by
  filter_upwards [hc] with ω hω t
  exact tsum_jump_transform_stoppedProcess hω (fun z ↦ if b < ‖z‖ then ‖z‖ else 0)
    (by simp only [norm_zero, ite_self]) τ t

end ProbabilityTheory
