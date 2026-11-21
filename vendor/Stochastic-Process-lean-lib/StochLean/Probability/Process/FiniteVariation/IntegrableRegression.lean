/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.IntegrableTerminal
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.ForMathlib.Probability.GaussianCriticalExponential

/-! # Integrable-variation boundary regressions

An unbounded deterministic ramp has infinite total variation even though
the totalized real conversion of that variation is the integrable zero
function. Conversely a random constant has zero variation even when its
initial value is not integrable. Neither boundary can be erased from the
terminal and Class D theorems.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory.IntegrableVariationRegression

private theorem ramp_variation_infinite :
    eVariationOn (fun t : ℝ≥0 ↦ (t : ℝ)) univ = ∞ := by
  by_contra h
  have hv : BoundedVariationOn (fun t : ℝ≥0 ↦ (t : ℝ)) univ := h
  let v := (eVariationOn (fun t : ℝ≥0 ↦ (t : ℝ)) univ).toReal
  let t : ℝ≥0 := ⟨v + 1, by dsimp [v]; positivity⟩
  have hd := hv.dist_le (mem_univ t) (mem_univ (0 : ℝ≥0))
  simp only [NNReal.coe_zero, dist_zero_right] at hd
  change |(t : ℝ)| ≤ v at hd
  have hb : (t : ℝ) ≤ v := (le_abs_self (t : ℝ)).trans hd
  change v + 1 ≤ v at hb
  linarith

/-- Totalized real variation being integrable does not imply integrable variation. -/
theorem infinite_variation_toReal_is_not_integrable_variation :
    Integrable (fun _ : Unit ↦
      (eVariationOn (fun t : ℝ≥0 ↦ (t : ℝ)) univ).toReal) (Measure.dirac ()) ∧
      ¬ HasIntegrableVariation (fun t (_ : Unit) ↦ (t : ℝ)) (Measure.dirac ()) := by
  constructor
  · simpa only [ramp_variation_infinite, ENNReal.toReal_top] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : Unit ↦ (0 : ℝ)) (Measure.dirac ()))
  · intro h
    have hf : ∀ᵐ ω : Unit ∂Measure.dirac (), False := by
      simpa only [ramp_variation_infinite, ne_eq, not_true_eq_false] using h.ae_eVariationOn_ne_top
    exact (ae_dirac_iff (by trivial)).mp hf

/-- An actual Gaussian random constant separates variation integrability
from the independent integrability of the initial value. -/
theorem exists_integrable_variation_not_integrable_initial :
    ∃ X : ℝ≥0 → ℝ → ℝ, HasIntegrableVariation X (gaussianReal 0 1) ∧
      ¬ Integrable (X 0) (gaussianReal 0 1) := by
  exact ⟨fun _ ω ↦ Real.exp (ω ^ 2 / 2), hasIntegrableVariation_const _,
    not_integrable_exp_half_sq_gaussianReal⟩

end ProbabilityTheory.IntegrableVariationRegression
