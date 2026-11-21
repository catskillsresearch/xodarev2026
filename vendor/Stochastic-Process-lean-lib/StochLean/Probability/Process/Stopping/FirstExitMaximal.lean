/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.FirstExit

/-! # First-exit reduction of a compact maximum event

A strict exceedance before a finite horizon forces the first-exit stopped value
to have norm at least the threshold. No no-overshoot assertion or measurability
of an uncountable supremum is assumed; the measure statement uses AE inclusion.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem le_norm_stoppedProcess_hittingAfter_of_exists {a : ℝ} {T : ℝ≥0} {ω : Ω}
    (hr : ProbabilityTheory.IsRightContinuousPath (X · ω))
    (hex : ∃ t ≤ T, a < ‖X t ω‖) :
    a ≤ ‖stoppedProcess X (hittingAfter X {x | a < ‖x‖} 0) T ω‖ := by
  obtain ⟨t, ht, hxt⟩ := hex
  have hhit : hittingAfter X {x | a < ‖x‖} 0 ω ≤ (T : WithTop ℝ≥0) :=
    (hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ t from bot_le) hxt).trans
      (WithTop.coe_le_coe.mpr ht)
  rw [stoppedProcess_eq_of_ge hhit]
  exact le_norm_hittingAfter_norm_of_ne_top hr
    (ne_top_of_le_ne_top WithTop.coe_ne_top hhit)

theorem measure_exists_norm_lt_le_firstExit_stopped {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (hr : ProbabilityTheory.HasRightContinuousPaths X P)
    (a : ℝ) (T : ℝ≥0) :
    P {ω | ∃ t ≤ T, a < ‖X t ω‖} ≤
      P {ω | a ≤ ‖stoppedProcess X (hittingAfter X {x | a < ‖x‖} 0) T ω‖} := by
  apply measure_mono_ae
  filter_upwards [hr] with ω hω
  exact le_norm_stoppedProcess_hittingAfter_of_exists hω

end MeasureTheory
