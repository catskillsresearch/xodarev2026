/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StoppedQuadraticPairLimit
public import StochLean.Analysis.PathVariation.CadlagC2JumpSeries
public import StochLean.Analysis.PathVariation.TaylorSums

/-! # Actual cadlag Taylor errors converge to the second-order jump correction -/

@[expose] public section

open Set Filter Function ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem tendsto_quadraticTaylorErrorSum_cadlag {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, quadraticVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsq : Summable (fun s : Ioc 0 T ↦ (x s - leftLim x s) ^ 2)) :
    Tendsto (fun n ↦ quadraticTaylorErrorSum (π n) f x T) atTop
      (𝓝 (∑' s : Ioc 0 T,
        (f (x s) - f (leftLim x s) - deriv f (leftLim x s) * (x s - leftLim x s) -
          deriv (deriv f) (leftLim x s) / 2 * (x s - leftLim x s) ^ 2))) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let Φ : ℝ → ℝ → ℝ := fun a b ↦ quadraticTaylorSlope f a b - deriv (deriv f) a / 2
  have hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2) :=
    (continuous_quadraticTaylorSlope_of_contDiff hf).sub
      ((hd.continuous_deriv_one.comp continuous_fst).div_const 2)
  have hs := (summable_abs_pair_weighted_sq_jumps hx hsq hΦ).of_abs
  have h := tendsto_quadraticPairSum_stopped_cadlag_jump_series π hx hΦ
    (fun a ↦ by simp only [Φ, quadraticTaylorSlope_self, sub_self]) hmesh hT hB hb hs
  simpa only [quadraticTaylorErrorSum, Φ, sub_mul, quadraticTaylorSlope_mul_sq] using h

end StochLean
