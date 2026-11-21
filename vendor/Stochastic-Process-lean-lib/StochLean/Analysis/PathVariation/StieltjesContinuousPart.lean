/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesSubmeasure
public import StochLean.ForMathlib.MeasureTheory.PointAtomicDecomposition

/-! # Continuous and jump parts of an increasing right-continuous path

Both parts start at zero and use the original Stieltjes measure. Continuity of
the diffuse part follows from the singleton/left-jump formula, including the
bottom endpoint. The original initial value remains a separate term.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

theorem continuous_stieltjes_of_nullSingletonClass (f : StieltjesFunction ℝ≥0)
    [NullSingletonClass f.measure] : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply f.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  have hr : rightLim f t = f t :=
    f.mono.continuousWithinAt_Ioi_iff_rightLim_eq.mp
      ((f.right_continuous t).mono Ioi_subset_Ici_self)
  have hz : ENNReal.ofReal (f t - leftLim f t) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_singleton]
  have hle := ENNReal.ofReal_eq_zero.mp hz
  have hge := f.mono.leftLim_le (le_refl t)
  have hl : leftLim f t = f t := by linarith
  exact hl.trans hr.symm

noncomputable def stieltjesContinuousPart (f : StieltjesFunction ℝ≥0) : StieltjesFunction ℝ≥0 :=
  stieltjesSubmeasure f (pointDiffusePart_le f.measure)

noncomputable def stieltjesJumpPart (f : StieltjesFunction ℝ≥0) : StieltjesFunction ℝ≥0 :=
  stieltjesSubmeasure f (pointAtomicPart_le f.measure)

@[simp] theorem stieltjesContinuousPart_zero (f : StieltjesFunction ℝ≥0) :
    stieltjesContinuousPart f 0 = 0 := stieltjesSubmeasure_zero _ _

@[simp] theorem stieltjesJumpPart_zero (f : StieltjesFunction ℝ≥0) :
    stieltjesJumpPart f 0 = 0 := stieltjesSubmeasure_zero _ _

theorem stieltjesContinuousPart_measure (f : StieltjesFunction ℝ≥0) :
    (stieltjesContinuousPart f).measure = pointDiffusePart f.measure :=
  stieltjesSubmeasure_measure _ _

theorem stieltjesJumpPart_measure (f : StieltjesFunction ℝ≥0) :
    (stieltjesJumpPart f).measure = pointAtomicPart f.measure :=
  stieltjesSubmeasure_measure _ _

theorem continuous_stieltjesContinuousPart (f : StieltjesFunction ℝ≥0) :
    Continuous (stieltjesContinuousPart f) := by
  have : NullSingletonClass (stieltjesContinuousPart f).measure := by
    rw [stieltjesContinuousPart_measure]
    infer_instance
  exact continuous_stieltjes_of_nullSingletonClass _

theorem stieltjesContinuousPart_add_jumpPart (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    stieltjesContinuousPart f t + stieltjesJumpPart f t = f t - f 0 := by
  have hsum := congrArg (fun μ : Measure ℝ≥0 ↦ μ.real (Iic t))
    (pointAtomicPart_add_pointDiffusePart f.measure)
  rw [measureReal_add_apply
    (stieltjesSubmeasure_Iic_lt_top f (pointAtomicPart_le f.measure) t).ne
    (stieltjesSubmeasure_Iic_lt_top f (pointDiffusePart_le f.measure) t).ne] at hsum
  change (pointAtomicPart f.measure).real (Iic t) +
    (pointDiffusePart f.measure).real (Iic t) = _ at hsum
  simp only [measureReal_def] at hsum
  rw [stieltjesMeasure_Iic_nnreal,
    ENNReal.toReal_ofReal
      (show 0 ≤ f t - f 0 from sub_nonneg.mpr (f.mono (show (0 : ℝ≥0) ≤ t from bot_le)))] at hsum
  exact (add_comm _ _).trans hsum

theorem stieltjesJumpPart_jump (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    stieltjesJumpPart f t - leftLim (stieltjesJumpPart f) t = f t - leftLim f t := by
  have h := pointAtomicPart_singleton f.measure t
  rw [← stieltjesJumpPart_measure, StieltjesFunction.measure_singleton,
    StieltjesFunction.measure_singleton] at h
  have hreal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal
    (sub_nonneg.mpr ((stieltjesJumpPart f).mono.leftLim_le le_rfl)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono.leftLim_le le_rfl))] using hreal

end StochLean
