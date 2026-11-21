/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesCovariationBound
public import StochLean.ForMathlib.MeasureTheory.StieltjesOrder

/-! # Quadratic domination of a covariation's variation measure

For every nonnegative scalar `r`, the measure inequality
`2 r |da| ≤ r² db + dc` follows from the interval Cauchy--Schwarz bound.
This is an inequality of measures on every measurable set, not only intervals.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

theorem totalVariationStieltjes_measure_quadratic_domination
    {a : ℝ≥0 → ℝ} (haBV : LocallyBoundedVariationOn a univ)
    (haRC : ∀ t, ContinuousWithinAt a (Ici t) t) (b c : StieltjesFunction ℝ≥0)
    (ha : ∀ s t, s ≤ t → |a t - a s| ≤ Real.sqrt (b t - b s) * Real.sqrt (c t - c s))
    (r : ℝ≥0) :
    (2 * r) • (totalVariationStieltjes a haBV haRC).measure ≤
      (r ^ 2) • b.measure + c.measure := by
  rw [← StieltjesFunction.measure_smul, ← StieltjesFunction.measure_smul,
    ← StieltjesFunction.measure_add]
  apply stieltjesMeasure_le_of_increment_le
  intro s t hst
  have htv := totalVariationStieltjes_measure_Ioc_le_of_covariation_increment_bound
    haBV haRC b.mono c.mono ha hst
  rw [StieltjesFunction.measure_Ioc] at htv
  have hv : (totalVariationStieltjes a haBV haRC) t -
      (totalVariationStieltjes a haBV haRC) s ≤
        Real.sqrt (b t - b s) * Real.sqrt (c t - c s) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htv
  have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * (r : ℝ) by positivity)
  have hB := Real.sq_sqrt (sub_nonneg.mpr (b.mono hst))
  have hC := Real.sq_sqrt (sub_nonneg.mpr (c.mono hst))
  have hBr := congrArg (fun z : ℝ ↦ (r : ℝ) ^ 2 * z) hB
  have hYoung := sq_nonneg ((r : ℝ) * Real.sqrt (b t - b s) - Real.sqrt (c t - c s))
  change (2 * (r : ℝ)) * (totalVariationStieltjes a haBV haRC) t -
      (2 * (r : ℝ)) * (totalVariationStieltjes a haBV haRC) s ≤
    ((r : ℝ) ^ 2 * b t + c t) - ((r : ℝ) ^ 2 * b s + c s)
  nlinarith only [hm, hC, hBr, hYoung]

end StochLean
