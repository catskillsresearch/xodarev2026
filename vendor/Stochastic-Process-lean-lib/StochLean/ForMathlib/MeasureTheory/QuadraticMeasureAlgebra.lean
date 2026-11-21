/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.QuadraticMeasureCauchySchwarz

/-! # Adding measure triples and initial atoms in quadratic domination -/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν ξ μ' ν' ξ' : Measure Ω}

theorem quadratic_measure_domination_add
    (h : ∀ r : ℝ≥0, (2 * r) • μ ≤ (r ^ 2) • ν + ξ)
    (h' : ∀ r : ℝ≥0, (2 * r) • μ' ≤ (r ^ 2) • ν' + ξ') (r : ℝ≥0) :
    (2 * r) • (μ + μ') ≤ (r ^ 2) • (ν + ν') + (ξ + ξ') := by
  simpa only [smul_add, add_assoc, add_comm, add_left_comm] using add_le_add (h r) (h' r)

theorem quadratic_measure_domination_scalar (κ : Measure Ω) (a b r : ℝ≥0) :
    (2 * r) • ((a * b) • κ) ≤ (r ^ 2) • ((a ^ 2) • κ) + (b ^ 2) • κ := by
  have hcoef : (2 * r) * (a * b) ≤ r ^ 2 * a ^ 2 + b ^ 2 := by
    apply NNReal.coe_le_coe.mp
    push_cast
    nlinarith only [sq_nonneg ((r : ℝ) * (a : ℝ) - (b : ℝ))]
  rw [smul_smul, smul_smul, ← add_smul]
  apply Measure.le_iff.mpr
  intro s _
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using
    mul_le_mul' (ENNReal.coe_le_coe.mpr hcoef) (le_rfl : κ s ≤ κ s)

end StochLean
