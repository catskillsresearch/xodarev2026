/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.IntervalAxioms
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # First moments of the actual Poisson counting process

The Poisson series gives the exact first moment, including rate zero.
The existing law and integrability interfaces transfer it to process values
and real increments. No martingale or bracket condition is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem integral_natCast_poisson (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  have hs := hasSum_integral_poissonMeasure (integrable_natCast_poisson r)
  rw [integral_poissonMeasure', hs.summable.tsum_eq_zero_add]
  · simp only [smul_eq_mul, Nat.cast_zero, mul_zero, zero_add]
    have he (n : ℕ) : Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
        ((n + 1).factorial : ℝ) * (n + 1 : ℕ) =
        (Real.exp (-(r : ℝ)) * (r : ℝ)) * ((r : ℝ) ^ n / (n.factorial : ℝ)) := by
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    simp_rw [he]
    rw [tsum_mul_left]
    have hexp : (∑' n : ℕ, (r : ℝ) ^ n / (n.factorial : ℝ)) = Real.exp r := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hexp, mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  · exact integrable_natCast_poisson r

theorem HasLaw.integral_natCast_poissonMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : Ω → ℕ} {r : ℝ≥0}
    (hY : HasLaw Y (poissonMeasure r) P) : (∫ ω, (Y ω : ℝ) ∂P) = r := by
  calc
    _ = ∫ n : ℕ, (n : ℝ) ∂poissonMeasure r := hY.integral_comp (by fun_prop)
    _ = r := integral_natCast_poisson r

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem IsPoissonProcess.integrable_real (hN : IsPoissonProcess N rate P) (t : ℝ≥0) :
    Integrable (fun ω ↦ (N t ω : ℝ)) P :=
  (hN.hasLaw t).integrable_natCast_poissonMeasure

theorem IsPoissonProcess.integral_real (hN : IsPoissonProcess N rate P) (t : ℝ≥0) :
    (∫ ω, (N t ω : ℝ) ∂P) = (rate : ℝ) * t := by
  exact (hN.hasLaw t).integral_natCast_poissonMeasure

theorem IsPoissonProcess.integrable_real_increment (hN : IsPoissonProcess N rate P) (s t : ℝ≥0) :
    Integrable (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) P :=
  (hN.integrable_real t).sub (hN.integrable_real s)

theorem IsPoissonProcess.integral_real_increment (hN : IsPoissonProcess N rate P) (s t : ℝ≥0) :
    (∫ ω, ((N t ω : ℝ) - (N s ω : ℝ)) ∂P) = (rate : ℝ) * ((t : ℝ) - s) := by
  rw [integral_sub (hN.integrable_real t) (hN.integrable_real s),
    hN.integral_real t, hN.integral_real s]
  ring

end ProbabilityTheory
