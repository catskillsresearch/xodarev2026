/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ExponentialJumpProduct

/-! # A zero-guarded complex-log representation of the real jump product

The principal complex logarithm retains the sign of negative factors.
Its convergent exponential represents the real product only when every
factor is nonzero. A separately summable count of jumps of size -1 supplies
the zero guard. This representation is intended for measurability proofs,
not as a replacement for the canonical real product definition.
-/

@[expose] public section

namespace StochLean

theorem summable_indicator_jump_neg_one {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    Summable (fun i ↦ if u i = -1 then (1 : ℝ) else 0) := by
  apply hu.of_norm_bounded
  intro i
  by_cases hi : u i = -1 <;> simp [hi, sq_nonneg]

theorem tsum_indicator_jump_neg_one_eq_zero_iff {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    (∑' i, if u i = -1 then (1 : ℝ) else 0) = 0 ↔ ∀ i, u i ≠ -1 := by
  classical
  constructor
  · intro hz i hi
    have h := (summable_indicator_jump_neg_one hu).sum_le_tsum {i}
      (fun j _ ↦ by split_ifs <;> norm_num)
    simp only [Finset.sum_singleton, if_pos hi, hz] at h
    norm_num at h
  · intro h
    simp only [if_neg (h _), tsum_zero]

theorem summable_complex_log_exponentialJumpFactor {ι : Type*} {u : ι → ℝ}
    (hu : Summable (fun i ↦ u i ^ 2)) :
    Summable (fun i ↦ Complex.log (exponentialJumpFactor (u i) : ℂ)) := by
  have h := Complex.summable_log_one_add_of_summable
    (Complex.summable_ofReal.mpr (summable_abs_exponentialJumpFactor_sub_one hu).of_abs)
  apply h.congr
  intro i
  congr 1
  push_cast
  ring

theorem tprod_exponentialJumpFactor_eq_re_cexp_tsum_log_of_ne_zero
    {ι : Type*} {u : ι → ℝ} (hu : Summable (fun i ↦ u i ^ 2))
    (hn : ∀ i, u i ≠ -1) :
    (∏' i, exponentialJumpFactor (u i)) =
      (Complex.exp (∑' i, Complex.log (exponentialJumpFactor (u i) : ℂ))).re := by
  have hfactor (i : ι) : (exponentialJumpFactor (u i) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact fun hz ↦ hn i ((exponentialJumpFactor_eq_zero_iff _).mp hz)
  have he := Complex.cexp_tsum_eq_tprod hfactor (summable_complex_log_exponentialJumpFactor hu)
  have hm := (multipliable_exponentialJumpFactor hu).map_tprod
    Complex.ofRealHom Complex.continuous_ofReal
  exact (congrArg Complex.re hm).trans (congrArg Complex.re he.symm)

theorem tprod_exponentialJumpFactor_eq_zero_guarded_complex_log
    {ι : Type*} {u : ι → ℝ} (hu : Summable (fun i ↦ u i ^ 2)) :
    (∏' i, exponentialJumpFactor (u i)) =
      if (∑' i, if u i = -1 then (1 : ℝ) else 0) = 0 then
        (Complex.exp (∑' i, Complex.log (exponentialJumpFactor (u i) : ℂ))).re else 0 := by
  classical
  by_cases hn : ∀ i, u i ≠ -1
  · rw [if_pos ((tsum_indicator_jump_neg_one_eq_zero_iff hu).mpr hn)]
    exact tprod_exponentialJumpFactor_eq_re_cexp_tsum_log_of_ne_zero hu hn
  · rw [if_neg (fun h ↦ hn ((tsum_indicator_jump_neg_one_eq_zero_iff hu).mp h))]
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    exact tprod_of_exists_eq_zero ⟨i, by simp only [hi, exponentialJumpFactor_neg_one]⟩

end StochLean
