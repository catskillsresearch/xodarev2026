/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesJumpSum
public import StochLean.ForMathlib.MeasureTheory.PointDiffuseRestriction

/-! # Stopping commutes with the continuous and jump Stieltjes components

The stopped measure is exactly restriction through the stopping endpoint, with
the atom at that endpoint included. Initial values are still separate.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace StochLean

noncomputable def stieltjesStop (f : StieltjesFunction ℝ≥0) (a : ℝ≥0) :
    StieltjesFunction ℝ≥0 where
  toFun t := f (min t a)
  mono' := f.mono.comp (monotone_id.min monotone_const)
  right_continuous' t := by
    have hg : ContinuousWithinAt (fun u : ℝ≥0 ↦ min u a) (Ici t) t :=
      continuousWithinAt_id.min continuousWithinAt_const
    have hm : MapsTo (fun u : ℝ≥0 ↦ min u a) (Ici t) (Ici (min t a)) := by
      intro u hu
      change min t a ≤ min u a
      exact min_le_min (show t ≤ u from hu) le_rfl
    exact (f.right_continuous (min t a)).comp (f := fun u : ℝ≥0 ↦ min u a)
      hg hm

@[simp] theorem stieltjesStop_apply (f : StieltjesFunction ℝ≥0) (a t : ℝ≥0) :
    stieltjesStop f a t = f (min t a) := rfl

@[simp] theorem stieltjesStop_zero (f : StieltjesFunction ℝ≥0) (a : ℝ≥0) :
    stieltjesStop f a 0 = f 0 := by
  rw [stieltjesStop_apply, min_eq_left (show (0 : ℝ≥0) ≤ a from bot_le)]

theorem stieltjesStop_measure_Iic (f : StieltjesFunction ℝ≥0) (a t : ℝ≥0) :
    (stieltjesStop f a).measure (Iic t) = f.measure (Iic (min t a)) := by
  simp only [stieltjesMeasure_Iic_nnreal, stieltjesStop_apply,
    min_eq_left (show (0 : ℝ≥0) ≤ a from bot_le)]

theorem stieltjesStop_measure (f : StieltjesFunction ℝ≥0) (a : ℝ≥0) :
    (stieltjesStop f a).measure = f.measure.restrict (Iic a) := by
  have hu : (⋃ n : ℕ, Iic (n : ℝ≥0)) = univ := by
    ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨Nat.ceil t, Nat.le_ceil t⟩
  apply Measure.ext_of_iUnion_eq_univ hu
  intro n
  have : IsFiniteMeasure ((stieltjesStop f a).measure.restrict (Iic (n : ℝ≥0))) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
        exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro t
  simp only [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
    stieltjesStop_measure_Iic]

theorem stieltjesContinuousPart_stop (f : StieltjesFunction ℝ≥0) (a t : ℝ≥0) :
    stieltjesContinuousPart (stieltjesStop f a) t = stieltjesContinuousPart f (min t a) := by
  change (pointDiffusePart (stieltjesStop f a).measure).real (Iic t) =
    (pointDiffusePart f.measure).real (Iic (min t a))
  rw [stieltjesStop_measure, pointDiffusePart_restrict _ measurableSet_Iic,
    measureReal_restrict_apply measurableSet_Iic, Iic_inter_Iic]

theorem stieltjesJumpPart_stop (f : StieltjesFunction ℝ≥0) (a t : ℝ≥0) :
    stieltjesJumpPart (stieltjesStop f a) t = stieltjesJumpPart f (min t a) := by
  have h := stieltjesContinuousPart_add_jumpPart (stieltjesStop f a) t
  rw [stieltjesContinuousPart_stop, stieltjesStop_apply, stieltjesStop_zero] at h
  linarith [stieltjesContinuousPart_add_jumpPart f (min t a)]

end StochLean
