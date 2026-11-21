/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.QuadraticTaylorSlope
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Absolute C2 Taylor remainders of a square-summable real family

No enumeration is required. Compact control of the filled Taylor quotient
near zero suffices; a square-summable family has only finitely many large terms.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

theorem summable_abs_contDiff_zero_remainder_of_summable_sq
    {ι : Type*} {u : ι → ℝ} (hu : Summable (fun i ↦ u i ^ 2))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun i ↦ |f (u i) - f 0 - deriv f 0 * u i|) := by
  have hc : Continuous (fun x : ℝ ↦ quadraticTaylorSlope f 0 x) :=
    (continuous_quadraticTaylorSlope_of_contDiff hf).comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ :=
    ((show IsCompact (Icc (-1 : ℝ) 1) from isCompact_Icc).image hc).isBounded.exists_norm_le
  apply (hu.mul_left C).of_norm_bounded_eventually
  filter_upwards [hu.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with i hi
  have hm : u i ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith only [hi]
  have hb := hC _ (mem_image_of_mem (fun x ↦ quadraticTaylorSlope f 0 x) hm)
  have he := quadraticTaylorSlope_mul_sq f 0 (u i)
  simp only [sub_zero] at he
  rw [← he]
  simp only [Real.norm_eq_abs, abs_abs, abs_mul, abs_pow, sq_abs] at hb ⊢
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

end StochLean
