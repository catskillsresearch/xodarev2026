/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesContinuousPart

/-! # The jump part is the actual sum of positive-time jumps

The sum is indexed by every time in `(0,t]`, not an assumed enumeration of
jumps. Countable support and finite mass on compact intervals give summability.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

theorem stieltjesJumpPart_ofReal_eq_tsum (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    ENNReal.ofReal (stieltjesJumpPart f t) =
      ∑' s : Ioc 0 t, ENNReal.ofReal (f s - leftLim f s) := by
  calc
    _ = (stieltjesJumpPart f).measure (Ioc 0 t) := by
      rw [StieltjesFunction.measure_Ioc, stieltjesJumpPart_zero, sub_zero]
    _ = pointAtomicPart f.measure (Ioc 0 t) := by rw [stieltjesJumpPart_measure]
    _ = ∑' s : Ioc 0 t, f.measure {(s : ℝ≥0)} :=
      pointAtomicPart_apply_eq_tsum _ measurableSet_Ioc
    _ = _ := by simp_rw [StieltjesFunction.measure_singleton]

theorem summable_stieltjes_jumps (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    Summable (fun s : Ioc 0 t ↦ f s - leftLim f s) := by
  have hsum : (∑' s : Ioc 0 t, ENNReal.ofReal (f s - leftLim f s)) ≠ ∞ := by
    rw [← stieltjesJumpPart_ofReal_eq_tsum]
    exact ENNReal.ofReal_ne_top
  have h := ENNReal.summable_toReal hsum
  simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono.leftLim_le le_rfl))] using h

theorem stieltjesJumpPart_eq_tsum (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    stieltjesJumpPart f t = ∑' s : Ioc 0 t, (f s - leftLim f s) := by
  have h := congrArg ENNReal.toReal (stieltjesJumpPart_ofReal_eq_tsum f t)
  have hnonneg : 0 ≤ stieltjesJumpPart f t := by
    rw [← stieltjesJumpPart_zero f]
    exact (stieltjesJumpPart f).mono (show (0 : ℝ≥0) ≤ t from bot_le)
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)] at h
  simpa only [ENNReal.toReal_ofReal hnonneg,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono.leftLim_le le_rfl))] using h

theorem stieltjes_continuous_jump_decomposition (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    f t = f 0 + stieltjesContinuousPart f t + ∑' s : Ioc 0 t, (f s - leftLim f s) := by
  rw [← stieltjesJumpPart_eq_tsum]
  linarith [stieltjesContinuousPart_add_jumpPart f t]

theorem stieltjesJumpPart_eq_zero_of_continuous (f : StieltjesFunction ℝ≥0)
    (hf : Continuous f) (t : ℝ≥0) : stieltjesJumpPart f t = 0 := by
  rw [stieltjesJumpPart_eq_tsum]
  have hl (s : ℝ≥0) : leftLim f s = f s := hf.continuousAt.continuousWithinAt.leftLim_eq
  simp only [hl, sub_self, tsum_zero]

theorem stieltjesContinuousPart_eq_of_continuous (f : StieltjesFunction ℝ≥0)
    (hf : Continuous f) (t : ℝ≥0) : stieltjesContinuousPart f t = f t - f 0 := by
  have h := stieltjesContinuousPart_add_jumpPart f t
  simpa only [stieltjesJumpPart_eq_zero_of_continuous f hf t, add_zero] using h

end StochLean
