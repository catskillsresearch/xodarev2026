/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Moments

/-! # Second moments of Poisson counts

The series shift proves square integrability and the exact second moment.
Ordered real increments inherit both results from their existing Poisson law.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem integrable_natCast_sq_poisson (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (poissonMeasure r) := by
  have hs := integrable_poissonMeasure_iff.mp
    ((integrable_natCast_poisson r).add (integrable_const (1 : ℝ)))
  rw [integrable_poissonMeasure_iff, ← summable_nat_add_iff 1]
  refine (hs.mul_left (r : ℝ)).congr fun n ↦ ?_
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem integral_natCast_sq_poisson (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + r := by
  have hs := hasSum_integral_poissonMeasure (integrable_natCast_sq_poisson r)
  rw [integral_poissonMeasure' (integrable_natCast_sq_poisson r),
    hs.summable.tsum_eq_zero_add]
  simp only [smul_eq_mul, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_add]
  have he (n : ℕ) : Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) /
      ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
        (n.factorial : ℝ) * ((n : ℝ) + 1)) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  simp_rw [he]
  rw [tsum_mul_left]
  have hi := integral_poissonMeasure'
    ((integrable_natCast_poisson r).add (integrable_const (1 : ℝ)))
  simp only [Pi.add_apply, smul_eq_mul] at hi
  rw [← hi, integral_add (integrable_natCast_poisson r) (integrable_const (1 : ℝ)),
    integral_natCast_poisson]
  simp only [integral_const, probReal_univ, one_smul]
  ring

theorem HasLaw.integrable_natCast_sq_poissonMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : Ω → ℕ} {r : ℝ≥0}
    (hY : HasLaw Y (poissonMeasure r) P) : Integrable (fun ω ↦ (Y ω : ℝ) ^ 2) P := by
  have hmap : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (P.map Y) := by
    rw [hY.map_eq]
    exact integrable_natCast_sq_poisson r
  exact (integrable_map_measure (by fun_prop) hY.aemeasurable).mp hmap

theorem HasLaw.integral_natCast_sq_poissonMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : Ω → ℕ} {r : ℝ≥0}
    (hY : HasLaw Y (poissonMeasure r) P) :
    (∫ ω, (Y ω : ℝ) ^ 2 ∂P) = (r : ℝ) ^ 2 + r := by
  calc
    _ = ∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r := hY.integral_comp (by fun_prop)
    _ = (r : ℝ) ^ 2 + r := integral_natCast_sq_poisson r

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem IsPoissonProcess.integrable_real_increment_sq (hN : IsPoissonProcess N rate P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Integrable (fun ω ↦ ((N t ω : ℝ) - (N s ω : ℝ)) ^ 2) P := by
  refine (hN.incrementLaw s t hst).integrable_natCast_sq_poissonMeasure.congr ?_
  filter_upwards [hN.monotonePaths] with ω hω
  rw [Nat.cast_sub (hω hst)]

theorem IsPoissonProcess.integral_real_increment_sq (hN : IsPoissonProcess N rate P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, ((N t ω : ℝ) - (N s ω : ℝ)) ^ 2 ∂P) =
      ((rate : ℝ) * ((t : ℝ) - s)) ^ 2 + (rate : ℝ) * ((t : ℝ) - s) := by
  have he : (fun ω ↦ ((N t ω - N s ω : ℕ) : ℝ) ^ 2) =ᵐ[P]
      fun ω ↦ ((N t ω : ℝ) - (N s ω : ℝ)) ^ 2 := by
    filter_upwards [hN.monotonePaths] with ω hω
    rw [Nat.cast_sub (hω hst)]
  rw [← integral_congr_ae he, (hN.incrementLaw s t hst).integral_natCast_sq_poissonMeasure]
  simp only [NNReal.coe_mul, NNReal.coe_sub hst]

end ProbabilityTheory
