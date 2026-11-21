/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.RNDerivativeQuadraticDomination
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # A density Cauchy--Schwarz bound from quadratic measure domination

The proof takes a countable intersection over absolute rational scalars and
then extends a polynomial inequality by density. Sigma-finite measures need
not have finite total mass.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν ξ ρ : Measure Ω}
  [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ] [SigmaFinite ρ]

theorem toReal_rnDeriv_sq_le_of_quadratic_domination
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ)
    (hνρ : ν ≪ ρ) (hξρ : ξ ≪ ρ) :
    ∀ᵐ ω ∂ρ, (μ.rnDeriv ρ ω).toReal ^ 2 ≤
      (ν.rnDeriv ρ ω).toReal * (ξ.rnDeriv ρ ω).toReal := by
  have hrat : ∀ᵐ ω ∂ρ, ∀ q : ℚ,
      2 * |(q : ℝ)| * (μ.rnDeriv ρ ω).toReal ≤
        |(q : ℝ)| ^ 2 * (ν.rnDeriv ρ ω).toReal + (ξ.rnDeriv ρ ω).toReal :=
    ae_all_iff.mpr fun q ↦ toReal_rnDeriv_quadratic_domination
      ⟨|(q : ℝ)|, abs_nonneg _⟩ (h _) hνρ hξρ
  filter_upwards [hrat] with ω hω
  let A := (μ.rnDeriv ρ ω).toReal
  let B := (ν.rnDeriv ρ ω).toReal
  let C := (ξ.rnDeriv ρ ω).toReal
  have hpoly_rat (q : ℚ) : 0 ≤ B * ((q : ℝ) * (q : ℝ)) + (-2 * A) * (q : ℝ) + C := by
    have hq := hω q
    change 2 * |(q : ℝ)| * A ≤ |(q : ℝ)| ^ 2 * B + C at hq
    rw [sq_abs] at hq
    have hle := mul_le_mul_of_nonneg_right (le_abs_self (q : ℝ))
      (show 0 ≤ A from ENNReal.toReal_nonneg)
    nlinarith only [hq, hle]
  have hpoly (r : ℝ) : 0 ≤ B * (r * r) + (-2 * A) * r + C := by
    refine Rat.denseRange_cast.induction_on r ?_ hpoly_rat
    exact isClosed_le continuous_const (by fun_prop)
  have hd := discrim_le_zero hpoly
  simp only [discrim] at hd
  change A ^ 2 ≤ B * C
  nlinarith only [hd]

theorem toReal_rnDeriv_le_sqrt_mul_sqrt_of_quadratic_domination
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ)
    (hνρ : ν ≪ ρ) (hξρ : ξ ≪ ρ) :
    ∀ᵐ ω ∂ρ, (μ.rnDeriv ρ ω).toReal ≤
      Real.sqrt (ν.rnDeriv ρ ω).toReal * Real.sqrt (ξ.rnDeriv ρ ω).toReal := by
  filter_upwards [toReal_rnDeriv_sq_le_of_quadratic_domination h hνρ hξρ] with ω hω
  simpa only [Real.sqrt_mul ENNReal.toReal_nonneg] using Real.le_sqrt_of_sq_le hω

theorem rnDeriv_le_rpow_mul_rpow_of_quadratic_domination
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ)
    (hνρ : ν ≪ ρ) (hξρ : ξ ≪ ρ) :
    ∀ᵐ ω ∂ρ, μ.rnDeriv ρ ω ≤
      (ν.rnDeriv ρ ω) ^ (1 / 2 : ℝ) * (ξ.rnDeriv ρ ω) ^ (1 / 2 : ℝ) := by
  have hroot (z : ℝ≥0∞) (hz : z ≠ ⊤) :
      ENNReal.ofReal (Real.sqrt z.toReal) = z ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_toReal hz]
  filter_upwards [toReal_rnDeriv_le_sqrt_mul_sqrt_of_quadratic_domination h hνρ hξρ,
    Measure.rnDeriv_ne_top μ ρ, Measure.rnDeriv_ne_top ν ρ, Measure.rnDeriv_ne_top ξ ρ]
    with ω hω hμ hν hξ
  have he := ENNReal.ofReal_le_ofReal hω
  simpa only [ENNReal.ofReal_toReal hμ, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    hroot _ hν, hroot _ hξ] using he

end StochLean
