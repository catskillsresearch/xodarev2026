/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.MonotoneIntegralMeasure
public import StochLean.ForMathlib.MeasurableStieltjesNNReal
public import Mathlib.MeasureTheory.Measure.Dirac

/-! # The actual variation measure of a deterministic unit step

A unit step activated at positive time has total-variation Stieltjes measure
equal to the Dirac measure at that time. Activation at zero gives the constant
unit path, whose increment measure is zero: the initial value is not an atom
of the variation measure.

The proof uses the existing step expression, actual variation owner, and
initial-interval measure formulas. It compares against a finite Dirac or zero
measure directly, without assuming finiteness of the unknown measure first.
No new step, Stieltjes-function, or measure owner is defined.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace StochLean

/-- The actual increment variation measure of a unit step distinguishes
positive activation from an initial value at zero. The regularity witnesses
are those of the existing `totalVariationStieltjes` owner. -/
theorem totalVariationStieltjes_measure_step_Ici (T : ℝ≥0)
    (hv : LocallyBoundedVariationOn (fun t : ℝ≥0 ↦ if T ≤ t then (1 : ℝ) else 0) univ)
    (hr : ∀ t, ContinuousWithinAt (fun u : ℝ≥0 ↦ if T ≤ u then (1 : ℝ) else 0) (Ici t) t) :
    (totalVariationStieltjes (fun t ↦ if T ≤ t then (1 : ℝ) else 0) hv hr).measure =
      if T = 0 then 0 else Measure.dirac T := by
  classical
  have hm : Monotone (fun t : ℝ≥0 ↦ if T ≤ t then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hs : T ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      split_ifs <;> norm_num
  have hI (t : ℝ≥0) :
      (totalVariationStieltjes (fun t ↦ if T ≤ t then (1 : ℝ) else 0) hv hr).measure (Iic t) =
        ENNReal.ofReal ((if T ≤ t then (1 : ℝ) else 0) -
          (if T ≤ 0 then (1 : ℝ) else 0)) := by
    rw [stieltjesMeasure_Iic_nnreal]
    change ENNReal.ofReal (pathTotalVariation (fun t ↦ if T ≤ t then (1 : ℝ) else 0) t -
      pathTotalVariation (fun t ↦ if T ≤ t then (1 : ℝ) else 0) 0) = _
    rw [pathTotalVariation_zero, sub_zero, pathTotalVariation_of_monotone hm]
  by_cases hT : T = 0
  · rw [if_pos hT]
    symm
    apply Measure.ext_of_Iic
    intro t
    rw [hI]
    simp [hT]
  · rw [if_neg hT]
    symm
    apply Measure.ext_of_Iic
    intro t
    rw [hI, Measure.dirac_apply]
    simp only [if_neg (not_le_of_gt (pos_iff_ne_zero.mpr hT)), sub_zero,
      indicator_apply, mem_Iic, Pi.one_apply]
    split_ifs <;> norm_num

/-- A positive deterministic activation carries exactly one unit atom in
the existing total-variation Stieltjes measure. -/
theorem totalVariationStieltjes_measure_step_Ici_of_pos (T : ℝ≥0) (hT : 0 < T)
    (hv : LocallyBoundedVariationOn (fun t : ℝ≥0 ↦ if T ≤ t then (1 : ℝ) else 0) univ)
    (hr : ∀ t, ContinuousWithinAt (fun u : ℝ≥0 ↦ if T ≤ u then (1 : ℝ) else 0) (Ici t) t) :
    (totalVariationStieltjes (fun t ↦ if T ≤ t then (1 : ℝ) else 0) hv hr).measure =
      Measure.dirac T := by
  rw [totalVariationStieltjes_measure_step_Ici T hv hr, if_neg hT.ne']

/-- An initial unit value has zero increment variation, not a Dirac atom
at the initial endpoint. -/
theorem totalVariationStieltjes_measure_step_Ici_zero
    (hv : LocallyBoundedVariationOn (fun t : ℝ≥0 ↦ if 0 ≤ t then (1 : ℝ) else 0) univ)
    (hr : ∀ t, ContinuousWithinAt (fun u : ℝ≥0 ↦ if 0 ≤ u then (1 : ℝ) else 0) (Ici t) t) :
    (totalVariationStieltjes (fun t ↦ if 0 ≤ t then (1 : ℝ) else 0) hv hr).measure = 0 := by
  rw [totalVariationStieltjes_measure_step_Ici 0 hv hr, if_pos rfl]

end StochLean
