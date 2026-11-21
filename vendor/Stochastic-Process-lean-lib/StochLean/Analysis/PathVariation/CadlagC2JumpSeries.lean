/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CadlagCompositionBounds
public import StochLean.ForMathlib.Analysis.QuadraticTaylorSlope

/-! # Absolute C2 jump-remainder summability from square-summable jumps

Finite variation of the original path is not required. Compact cadlag
bounds and the actual quadratic Taylor quotient dominate each remainder
by a constant times its squared jump.
-/

@[expose] public section

open Set Function ProbabilityTheory
open scoped NNReal

namespace StochLean

theorem summable_abs_pair_weighted_sq_jumps {x : ℝ≥0 → ℝ}
    (hx : IsCadlagPath x) {T : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 T ↦ (x s - leftLim x s) ^ 2))
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2)) :
    Summable (fun s : Ioc 0 T ↦ |Φ (leftLim x s) (x s) * (x s - leftLim x s) ^ 2|) := by
  obtain ⟨C, _, hC⟩ := exists_compact_pair_bound_of_cadlag hx T hΦ
  apply (hs.mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs, abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (hC s ⟨s.2.1.le, s.2.2⟩) (sq_nonneg _)

theorem summable_abs_contDiff_jump_remainders_of_summable_sq {x : ℝ≥0 → ℝ}
    (hx : IsCadlagPath x) {T : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 T ↦ (x s - leftLim x s) ^ 2))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun s : Ioc 0 T ↦
      |f (x s) - f (leftLim x s) - deriv f (leftLim x s) * (x s - leftLim x s)|) := by
  simpa only [quadraticTaylorSlope_mul_sq] using summable_abs_pair_weighted_sq_jumps hx hs
    (continuous_quadraticTaylorSlope_of_contDiff hf)

theorem summable_abs_contDiff_second_order_jump_remainders {x : ℝ≥0 → ℝ}
    (hx : IsCadlagPath x) {T : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 T ↦ (x s - leftLim x s) ^ 2))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun s : Ioc 0 T ↦
      |f (x s) - f (leftLim x s) - deriv f (leftLim x s) * (x s - leftLim x s) -
        deriv (deriv f) (leftLim x s) / 2 * (x s - leftLim x s) ^ 2|) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h := summable_abs_pair_weighted_sq_jumps hx hs
    (Φ := fun a b ↦ quadraticTaylorSlope f a b - deriv (deriv f) a / 2)
    ((continuous_quadraticTaylorSlope_of_contDiff hf).sub
      ((hd.continuous_deriv_one.comp continuous_fst).div_const 2))
  simpa only [sub_mul, quadraticTaylorSlope_mul_sq] using h

end StochLean
