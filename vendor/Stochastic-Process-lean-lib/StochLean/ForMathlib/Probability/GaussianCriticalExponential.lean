/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Failure of integrability at the Gaussian quadratic-exponential threshold

Multiplying exp(x^2/2) by the standard Gaussian density gives a strictly
positive constant on the whole real line. Its expectation therefore fails
to exist as an integrable random variable, despite its smoothness and positivity.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

theorem not_integrable_exp_half_sq_gaussianReal :
    ¬ Integrable (fun x : ℝ ↦ Real.exp (x ^ 2 / 2)) (gaussianReal 0 1) := by
  intro h
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0)] at h
  have hi := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Filter.Eventually.of_forall (fun _ ↦ gaussianPDF_lt_top))).1 h
  have he (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    have hz : -(x ^ 2) / 2 + x ^ 2 / 2 = 0 := by ring
    rw [hz, Real.exp_zero, mul_one]
  have hc : Integrable (fun _ : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹) volume := by
    simpa only [toReal_gaussianPDF, smul_eq_mul, he] using hi
  have hn : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  have : IsFiniteMeasure (volume : Measure ℝ) :=
    (integrable_const_iff_isFiniteMeasure hn).1 hc
  exact (measure_ne_top (volume : Measure ℝ) Set.univ) Real.volume_univ

end ProbabilityTheory
