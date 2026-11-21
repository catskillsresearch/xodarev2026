/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.RNDerivativeOrder

/-! # Quadratic measure domination transfers to Radon--Nikodym densities -/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν ξ ρ : Measure Ω}
  [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ] [SigmaFinite ρ]

theorem rnDeriv_quadratic_domination (r : ℝ≥0)
    (h : (2 * r) • μ ≤ (r ^ 2) • ν + ξ) (hνρ : ν ≪ ρ) (hξρ : ξ ≪ ρ) :
    ∀ᵐ ω ∂ρ, ((2 * r : ℝ≥0) : ℝ≥0∞) * μ.rnDeriv ρ ω ≤
      ((r ^ 2 : ℝ≥0) : ℝ≥0∞) * ν.rnDeriv ρ ω + ξ.rnDeriv ρ ω := by
  have hle := rnDeriv_le_of_measure_le h ((hνρ.smul_left (r ^ 2)).add_left hξρ)
  filter_upwards [hle, Measure.rnDeriv_smul_left' μ ρ (2 * r),
    Measure.rnDeriv_add' ((r ^ 2) • ν) ξ ρ, Measure.rnDeriv_smul_left' ν ρ (r ^ 2)]
    with ω hω hμ hsum hν
  have hpoint : (2 * r) • μ.rnDeriv ρ ω ≤ (r ^ 2) • ν.rnDeriv ρ ω + ξ.rnDeriv ρ ω := by
    simpa only [hμ, hsum, Pi.add_apply, hν, Pi.smul_apply] using hω
  simpa only [ENNReal.smul_def, smul_eq_mul] using hpoint

theorem toReal_rnDeriv_quadratic_domination (r : ℝ≥0)
    (h : (2 * r) • μ ≤ (r ^ 2) • ν + ξ) (hνρ : ν ≪ ρ) (hξρ : ξ ≪ ρ) :
    ∀ᵐ ω ∂ρ, 2 * (r : ℝ) * (μ.rnDeriv ρ ω).toReal ≤
      (r : ℝ) ^ 2 * (ν.rnDeriv ρ ω).toReal + (ξ.rnDeriv ρ ω).toReal := by
  filter_upwards [rnDeriv_quadratic_domination r h hνρ hξρ,
    Measure.rnDeriv_ne_top ν ρ, Measure.rnDeriv_ne_top ξ ρ] with ω hω hν hξ
  have hm : ((r ^ 2 : ℝ≥0) : ℝ≥0∞) * ν.rnDeriv ρ ω ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hν
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hm, hξ⟩) hω
  simpa only [ENNReal.toReal_add hm hξ, ENNReal.toReal_mul, ENNReal.coe_toReal,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow] using ht

end StochLean
