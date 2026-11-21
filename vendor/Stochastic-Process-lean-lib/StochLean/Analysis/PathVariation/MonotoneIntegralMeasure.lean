/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegral

/-! # The existing pathwise integral of a Stieltjes function uses its own measure

Canonical positive variation is the original path minus its initial value;
negative variation is zero. The initial integral term remains separate.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace StochLean

theorem pathTotalVariation_of_monotone {x : ℝ≥0 → ℝ} (hx : Monotone x) (t : ℝ≥0) :
    pathTotalVariation x t = x t - x 0 := by
  have h : eVariationOn x (Icc 0 t) = ENNReal.ofReal (x t - x 0) := by
    simpa only [univ_inter] using (hx.monotoneOn univ).eVariationOn_eq (mem_univ 0) (mem_univ t)
  rw [pathTotalVariation_eq, h,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hx (show 0 ≤ t from bot_le)))]

theorem positiveVariationStieltjes_measure_of_stieltjes (A : StieltjesFunction ℝ≥0)
    (hv : LocallyBoundedVariationOn A univ) :
    (positiveVariationStieltjes A hv A.right_continuous).measure = A.measure := by
  have he : positiveVariationStieltjes A hv A.right_continuous +
      StieltjesFunction.const ℝ≥0 (A 0) = A := by
    apply StieltjesFunction.ext
    intro t
    change pathPositiveVariation A t + A 0 = A t
    rw [pathPositiveVariation, pathTotalVariation_of_monotone A.mono]
    ring
  have h := congrArg (fun B : StieltjesFunction ℝ≥0 ↦ B.measure) he
  simpa only [StieltjesFunction.measure_add, StieltjesFunction.measure_const, add_zero] using h

theorem negativeVariationStieltjes_measure_of_stieltjes (A : StieltjesFunction ℝ≥0)
    (hv : LocallyBoundedVariationOn A univ) :
    (negativeVariationStieltjes A hv A.right_continuous).measure = 0 := by
  have he : negativeVariationStieltjes A hv A.right_continuous = 0 := by
    apply StieltjesFunction.ext
    intro t
    change pathNegativeVariation A t = 0
    rw [pathNegativeVariation, pathTotalVariation_of_monotone A.mono]
    ring
  rw [he, StieltjesFunction.measure_zero]

theorem totalVariationStieltjes_measure_of_stieltjes (A : StieltjesFunction ℝ≥0)
    (hv : LocallyBoundedVariationOn A univ) :
    (totalVariationStieltjes A hv A.right_continuous).measure = A.measure := by
  rw [totalVariationStieltjes_measure_eq_add, positiveVariationStieltjes_measure_of_stieltjes,
    negativeVariationStieltjes_measure_of_stieltjes, add_zero]

theorem pathStieltjesIncrementIntegral_eq_stieltjesIntegral (A : StieltjesFunction ℝ≥0)
    (hv : LocallyBoundedVariationOn A univ) (H : ℝ≥0 → ℝ) (s t : ℝ≥0) :
    pathStieltjesIncrementIntegral A hv A.right_continuous H s t =
      ∫ u in Ioc s t, H u ∂A.measure := by
  rw [pathStieltjesIncrementIntegral, positiveVariationStieltjes_measure_of_stieltjes,
    negativeVariationStieltjes_measure_of_stieltjes]
  simp only [Measure.restrict_zero, integral_zero_measure, sub_zero]

theorem pathStieltjesIntegral_eq_stieltjesIntegral (A : StieltjesFunction ℝ≥0)
    (hv : LocallyBoundedVariationOn A univ) (H : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathStieltjesIntegral A hv A.right_continuous H t =
      H 0 * A 0 + ∫ u in Ioc 0 t, H u ∂A.measure := by
  rw [pathStieltjesIntegral, pathStieltjesIncrementIntegral_eq_stieltjesIntegral]

end StochLean
