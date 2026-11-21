/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesKunitaWatanabe
public import StochLean.ForMathlib.MeasureTheory.WeightedMeasureInitialAtom

/-! # The Stieltjes weighted bound with an explicit initial contribution -/

@[expose] public section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

theorem stieltjes_lintegral_mul_le_with_initial_atom
    {a : ℝ≥0 → ℝ} (haBV : LocallyBoundedVariationOn a univ)
    (haRC : ∀ t, ContinuousWithinAt a (Ici t) t) (b c : StieltjesFunction ℝ≥0)
    (ha : ∀ s t, s ≤ t → |a t - a s| ≤ Real.sqrt (b t - b s) * Real.sqrt (c t - c s))
    (a₀ b₀ : ℝ≥0) {f g : ℝ≥0 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ((a₀ * b₀ : ℝ≥0) : ℝ≥0∞) * (f 0 * g 0) +
      (∫⁻ t, f t * g t ∂(totalVariationStieltjes a haBV haRC).measure) ≤
      (((a₀ ^ 2 : ℝ≥0) : ℝ≥0∞) * (f 0) ^ 2 + (∫⁻ t, (f t) ^ 2 ∂b.measure)) ^ (1 / 2 : ℝ) *
        (((b₀ ^ 2 : ℝ≥0) : ℝ≥0∞) * (g 0) ^ 2 + (∫⁻ t, (g t) ^ 2 ∂c.measure)) ^ (1 / 2 : ℝ) :=
  lintegral_mul_le_with_initial_atom
    (totalVariationStieltjes_measure_quadratic_domination haBV haRC b c ha) 0 a₀ b₀ hf hg

end StochLean
