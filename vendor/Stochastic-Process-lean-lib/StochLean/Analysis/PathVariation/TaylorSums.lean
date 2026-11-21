/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.QuadraticPairSums
public import StochLean.ForMathlib.Analysis.QuadraticTaylorSlope

/-! # Exact second-order Taylor sums with retained partial cells -/

@[expose] public section

open Set Filter Finset
open scoped NNReal Topology

namespace StochLean

noncomputable def quadraticTaylorErrorSum {S : ℝ≥0} (π : TimePartition S)
    (f : ℝ → ℝ) (x : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  quadraticPairSum π (fun a b ↦ quadraticTaylorSlope f a b - deriv (deriv f) a / 2) x

theorem TimePartition.taylor_sum_with_remainder {S : ℝ≥0} (π : TimePartition S)
    (f : ℝ → ℝ) (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    f (x (min S t)) - f (x 0) =
      (∑ i : Fin π.size, deriv f (x (π.left i)) *
        (x (min (π.right i) t) - x (min (π.left i) t))) +
      (1 / 2 : ℝ) * (∑ i : Fin π.size, deriv (deriv f) (x (π.left i)) *
        (x (min (π.right i) t) - x (min (π.left i) t)) ^ 2) +
      quadraticTaylorErrorSum π f x t := by
  have ht : (∑ i : Fin π.size,
      (f (x (min (π.right i) t)) - f (x (min (π.left i) t)))) =
      f (x (min S t)) - f (x 0) := by
    simpa only [TimePartition.increment, zero_min] using
      π.sum_increment (fun u ↦ f (x (min u t)))
  rw [← ht, quadraticTaylorErrorSum, quadraticPairSum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : π.left i ≤ t
  · rw [min_eq_left hi]
    have h := quadraticTaylorSlope_mul_sq f (x (π.left i)) (x (min (π.right i) t))
    linear_combination -h
  · have hl : t ≤ π.left i := (lt_of_not_ge hi).le
    have hr : t ≤ π.right i := hl.trans (π.left_le_right i)
    simp only [min_eq_right hl, min_eq_right hr, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero]

theorem tendstoUniformlyOn_quadraticTaylorErrorSum_zero {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T,
      quadraticVariationSum (π n) (fun u ↦ x (min u t)) ≤ B) :
    TendstoUniformlyOn (fun n ↦ quadraticTaylorErrorSum (π n) f x)
      (fun _ ↦ 0) atTop (Icc 0 T) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact tendstoUniformlyOn_quadraticPairSum_zero π hx
    ((continuous_quadraticTaylorSlope_of_contDiff hf).sub
      ((hd.continuous_deriv_one.comp continuous_fst).div_const 2))
    (fun a ↦ by rw [quadraticTaylorSlope_self, sub_self]) hmesh hB hb

end StochLean
