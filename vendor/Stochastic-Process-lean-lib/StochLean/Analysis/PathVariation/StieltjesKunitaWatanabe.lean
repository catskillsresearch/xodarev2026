/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesCovariationDomination
public import StochLean.ForMathlib.MeasureTheory.QuadraticMeasureCauchySchwarz

/-! # The deterministic Lebesgue--Stieltjes theorem behind Kunita--Watanabe

Protter II.24: an interval Cauchy--Schwarz bound implies the weighted bound
for the total-variation measure and absolute continuity with respect to
both increasing component measures. Weights may be unbounded, and energies
may be infinite. Initial values are irrelevant to these increment measures.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

variable {a : ℝ≥0 → ℝ} (haBV : LocallyBoundedVariationOn a univ)
  (haRC : ∀ t, ContinuousWithinAt a (Ici t) t) (b c : StieltjesFunction ℝ≥0)
  (ha : ∀ s t, s ≤ t → |a t - a s| ≤ Real.sqrt (b t - b s) * Real.sqrt (c t - c s))

include ha

theorem stieltjes_lintegral_mul_le_of_increment_bound
    {f g : ℝ≥0 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ t, f t * g t ∂(totalVariationStieltjes a haBV haRC).measure) ≤
      (∫⁻ t, (f t) ^ 2 ∂b.measure) ^ (1 / 2 : ℝ) *
        (∫⁻ t, (g t) ^ 2 ∂c.measure) ^ (1 / 2 : ℝ) :=
  lintegral_mul_le_of_quadratic_measure_domination
    (totalVariationStieltjes_measure_quadratic_domination haBV haRC b c ha) hf hg

theorem totalVariationStieltjes_absolutelyContinuous_left_of_increment_bound :
    (totalVariationStieltjes a haBV haRC).measure ≪ b.measure :=
  absolutelyContinuous_left_of_quadratic_measure_domination
    (totalVariationStieltjes_measure_quadratic_domination haBV haRC b c ha)

theorem totalVariationStieltjes_absolutelyContinuous_right_of_increment_bound :
    (totalVariationStieltjes a haBV haRC).measure ≪ c.measure :=
  absolutelyContinuous_right_of_quadratic_measure_domination
    (totalVariationStieltjes_measure_quadratic_domination haBV haRC b c ha)

end StochLean
