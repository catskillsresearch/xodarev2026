/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.QuadraticMeasureAlgebra

/-! # Weighted quadratic domination including a separate initial atom

This preserves the initial term when the half-line integration convention
includes it, without changing the underlying increment Stieltjes measures.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν ξ : Measure Ω}
  [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]

theorem lintegral_mul_le_with_initial_atom
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ)
    (ω₀ : Ω) (a b : ℝ≥0) {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ((a * b : ℝ≥0) : ℝ≥0∞) * (f ω₀ * g ω₀) + (∫⁻ ω, f ω * g ω ∂μ) ≤
      (((a ^ 2 : ℝ≥0) : ℝ≥0∞) * (f ω₀) ^ 2 + (∫⁻ ω, (f ω) ^ 2 ∂ν)) ^ (1 / 2 : ℝ) *
        (((b ^ 2 : ℝ≥0) : ℝ≥0∞) * (g ω₀) ^ 2 + (∫⁻ ω, (g ω) ^ 2 ∂ξ)) ^ (1 / 2 : ℝ) := by
  have haug := lintegral_mul_le_of_quadratic_measure_domination
    (quadratic_measure_domination_add
      (quadratic_measure_domination_scalar (Measure.dirac ω₀) a b) h)
    hf hg
  simpa only [lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac' ω₀ (f := fun ω ↦ f ω * g ω) (hf.mul hg),
    lintegral_dirac' ω₀ (hf.pow_const 2),
    lintegral_dirac' ω₀ (hg.pow_const 2), ENNReal.smul_def, smul_eq_mul] using haug

end StochLean
