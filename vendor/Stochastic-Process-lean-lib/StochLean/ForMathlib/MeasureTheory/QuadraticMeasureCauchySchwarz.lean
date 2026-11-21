/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.WeightedDensityCauchySchwarz

/-! # Weighted Cauchy--Schwarz from quadratic domination of three measures

The sum of the three sigma-finite measures provides an actual dominating
measure. Arbitrary measurable extended nonnegative weights are permitted.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν ξ : Measure Ω}
  [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]

theorem lintegral_mul_le_of_quadratic_measure_domination
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ)
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, f ω * g ω ∂μ) ≤
      (∫⁻ ω, (f ω) ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, (g ω) ^ 2 ∂ξ) ^ (1 / 2 : ℝ) := by
  let ρ := μ + ν + ξ
  have hμρ : μ ≪ ρ := ((Measure.AbsolutelyContinuous.refl μ).add_right ν).add_right ξ
  have hνρ : ν ≪ ρ := ((Measure.AbsolutelyContinuous.refl ν).add_right' μ).add_right ξ
  have hξρ : ξ ≪ ρ := (Measure.AbsolutelyContinuous.refl ξ).add_right' (μ + ν)
  exact lintegral_mul_le_of_rnDeriv_cauchySchwarz hμρ hνρ hξρ
    (rnDeriv_le_rpow_mul_rpow_of_quadratic_domination h hνρ hξρ) hf hg

theorem absolutelyContinuous_left_of_quadratic_measure_domination
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ) : μ ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  have hcs := lintegral_mul_le_of_quadratic_measure_domination h
    (f := s.indicator (fun _ ↦ (1 : ℝ≥0∞))) (g := fun _ ↦ (1 : ℝ≥0∞))
    (measurable_const.indicator hs) measurable_const
  have hsq (ω : Ω) : (s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω) ^ 2 =
      s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    by_cases hω : ω ∈ s <;> simp [hω]
  simp only [hsq] at hcs
  simpa [hs, hzero] using hcs

theorem absolutelyContinuous_right_of_quadratic_measure_domination
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ) : μ ≪ ξ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  have hcs := lintegral_mul_le_of_quadratic_measure_domination h
    (f := fun _ ↦ (1 : ℝ≥0∞)) (g := s.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    measurable_const (measurable_const.indicator hs)
  have hsq (ω : Ω) : (s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω) ^ 2 =
      s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    by_cases hω : ω ∈ s <;> simp [hω]
  simp only [hsq] at hcs
  simpa [hs, hzero] using hcs

end StochLean
