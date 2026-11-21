/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Approximation

/-! # Decreasing dyadic subsequences of the existing upper approximations

The full right-grid sequence with denominator n+1 need not be decreasing.
The source dyadic subsequence is nested. No new stopping approximation owner
is introduced: capped times remain `upperApprox T (2^n - 1)`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology

namespace ProbabilityTheory

theorem antitone_dyadicRightGrid (t : ℝ≥0) : Antitone (fun n ↦ dyadicRightGrid n t) := by
  apply antitone_nat_of_succ_le
  intro n
  have hscale : ((2 ^ (n + 1) : ℕ) : ℝ≥0) = 2 * ((2 ^ n : ℕ) : ℝ≥0) := by
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hc : Nat.ceil (((2 ^ (n + 1) : ℕ) : ℝ≥0) * t) ≤
      2 * Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_mul, Nat.cast_ofNat, hscale, mul_assoc]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
  rw [dyadicRightGrid_eq, dyadicRightGrid_eq, div_le_iff₀ (by positivity)]
  calc
    _ ≤ (2 : ℝ≥0) * Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) := by exact_mod_cast hc
    _ = _ := by
      rw [hscale]
      field_simp

theorem FiniteStoppingTime.antitone_dyadic_upperApprox
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (ω : Ω) :
    Antitone (fun n ↦ τ.upperApprox T (2 ^ n - 1) ω) := by
  intro i j hij
  exact min_le_min ((antitone_dyadicRightGrid (τ ω)) hij) le_rfl

theorem FiniteStoppingTime.tendsto_dyadic_upperApprox
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) (ω : Ω) :
    Tendsto (fun n ↦ τ.upperApprox T (2 ^ n - 1) ω) atTop
      (nhdsWithin (τ ω) (Set.Ici (τ ω))) :=
  (τ.tendsto_upperApprox hb ω).comp ((tendsto_sub_atTop_nat 1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by norm_num)))

/-- Upper approximation preserves the order of two stopping times. This
monotonicity is in the time input, not in the general mesh index. -/
theorem FiniteStoppingTime.upperApprox_mono
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    (σ τ : FiniteStoppingTime F) (hle : ∀ ω, σ ω ≤ τ ω) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    σ.upperApprox T n ω ≤ τ.upperApprox T n ω := by
  apply min_le_min ?_ le_rfl
  unfold rightGrid
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left (hle ω) (by positivity))

end ProbabilityTheory
