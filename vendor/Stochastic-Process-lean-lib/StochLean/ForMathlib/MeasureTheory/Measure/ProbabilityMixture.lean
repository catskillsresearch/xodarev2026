/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Countable probability mixtures and positive-weight domination -/

@[expose] public section

open scoped NNReal ENNReal

namespace MeasureTheory.Measure

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

theorem isProbabilityMeasure_probability_mixture [Countable ι] (P : ι → Measure Ω)
    [∀ k, IsProbabilityMeasure (P k)] (c : ι → ℝ≥0)
    (hc : (∑' k, (c k : ℝ≥0∞)) = 1) :
    IsProbabilityMeasure (Measure.sum (fun k ↦ (c k : ℝ≥0∞) • P k)) := by
  constructor
  simpa only [sum_apply_of_countable, smul_apply, measure_univ, smul_eq_mul, mul_one] using hc

theorem absolutelyContinuous_probability_mixture (P : ι → Measure Ω) (c : ι → ℝ≥0)
    {k : ι} (hk : c k ≠ 0) :
    P k ≪ Measure.sum (fun j ↦ (c j : ℝ≥0∞) • P j) :=
  absolutelyContinuous_sum_right k (absolutelyContinuous_smul (by exact_mod_cast hk))

end MeasureTheory.Measure
