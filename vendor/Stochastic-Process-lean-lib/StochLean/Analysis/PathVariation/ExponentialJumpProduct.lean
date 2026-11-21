/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ExponentialJumpFactor

/-! # Zero factors and the two equivalent stochastic-exponential products

The nonvanishing criterion uses absolute convergence of deviations from
one. The raw-bracket compensation is the exponential of the actual sum
of squared jumps, including when a factor vanishes or is negative.
-/

@[expose] public section

namespace StochLean

theorem tprod_exponentialJumpFactor_ne_zero_iff {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    (∏' i, exponentialJumpFactor (u i)) ≠ 0 ↔ ∀ i, u i ≠ -1 := by
  constructor
  · intro h i hi
    exact h (tprod_of_exists_eq_zero ⟨i, by simp only [hi, exponentialJumpFactor_neg_one]⟩)
  · intro h
    have hn (i : ι) : 1 + (exponentialJumpFactor (u i) - 1) ≠ 0 := by
      have he : 1 + (exponentialJumpFactor (u i) - 1) = exponentialJumpFactor (u i) := by ring
      rw [he]
      exact fun hz ↦ h i ((exponentialJumpFactor_eq_zero_iff _).mp hz)
    have hs : Summable (fun i ↦ ‖exponentialJumpFactor (u i) - 1‖) := by
      simpa only [Real.norm_eq_abs] using summable_abs_exponentialJumpFactor_sub_one hu
    have he : (fun i ↦ 1 + (exponentialJumpFactor (u i) - 1)) =
        fun i ↦ exponentialJumpFactor (u i) := by funext i; ring
    simpa only [he] using tprod_one_add_ne_zero_of_summable hn hs

theorem multipliable_compensatedExponentialJumpFactor {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    Multipliable (fun i ↦ (1 + u i) * Real.exp (-u i + (1 / 2 : ℝ) * u i ^ 2)) := by
  have he := ((hu.mul_left (1 / 2)).hasSum.rexp).multipliable
  have h := (multipliable_exponentialJumpFactor hu).mul he
  apply h.congr
  intro i
  simp only [exponentialJumpFactor, Real.exp_add, mul_assoc, Function.comp_apply]

theorem tprod_compensatedExponentialJumpFactor {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    (∏' i, (1 + u i) * Real.exp (-u i + (1 / 2 : ℝ) * u i ^ 2)) =
      (∏' i, exponentialJumpFactor (u i)) * Real.exp ((1 / 2 : ℝ) * ∑' i, u i ^ 2) := by
  have he := ((hu.mul_left (1 / 2)).hasSum.rexp)
  have h := (multipliable_exponentialJumpFactor hu).hasProd.mul he
  have ht : HasProd
      (fun i ↦ (1 + u i) * Real.exp (-u i + (1 / 2 : ℝ) * u i ^ 2))
      ((∏' i, exponentialJumpFactor (u i)) * Real.exp (∑' i, (1 / 2 : ℝ) * u i ^ 2)) := by
    simpa only [exponentialJumpFactor, Real.exp_add, mul_assoc, Function.comp_apply] using h
  simpa only [tsum_mul_left] using ht.tprod_eq

end StochLean
