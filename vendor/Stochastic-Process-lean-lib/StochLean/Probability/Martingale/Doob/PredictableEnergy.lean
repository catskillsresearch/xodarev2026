/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.Supermartingale
public import StochLean.Probability.Moments.L2
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Second-moment estimates for discrete predictable increasing processes

The finite square-integrable calculation underlying Protter III.10, Lemma 1
(printed p.108). The later truncation argument must derive, not assume, the
terminal second moment. This module introduces no compensator selector.
-/

@[expose] public section

open ProbabilityTheory Filter Finset
open scoped ENNReal

namespace MeasureTheory

private theorem sq_sub_le_twice_sum_remaining (x : ℕ → ℝ) (n : ℕ) :
    (x n - x 0) ^ 2 ≤
      2 * ∑ k ∈ range n, (x n - x k) * (x (k + 1) - x k) := by
  have he : (∑ k ∈ range n, ((x n - x k) ^ 2 - (x n - x (k + 1)) ^ 2)) =
      (x n - x 0) ^ 2 := by
    rw [sum_range_sub']
    ring
  rw [← he, mul_sum]
  exact sum_le_sum fun k _ ↦ by nlinarith [sq_nonneg (x (k + 1) - x k)]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℕ mΩ} {C : ℕ → Ω → ℝ}

/-- Finite L2 stage of the predictable increasing-process energy bound.
The square-integrability premises are removed by truncation in the terminal theorem. -/
theorem IsStronglyPredictable.integral_sq_le_of_condExp_tail_bound
    (hp : IsStronglyPredictable F C) (hm : HasMonotonePaths C P)
    (h0 : C 0 =ᵐ[P] 0) (hL : ∀ k, MemLp (C k) 2 P) {N : ℝ} (hN : 0 ≤ N)
    (n : ℕ) (hb : ∀ k ≤ n, P[C n - C k | F k] ≤ᵐ[P] (fun _ ↦ N)) :
    (∫ ω, C n ω ^ 2 ∂P) ≤ 2 * N ^ 2 := by
  have hi (k : ℕ) : Integrable (C k) P := (hL k).integrable (by norm_num)
  have hE : (∫ ω, C n ω ∂P) ≤ N := by
    have hb0 := integral_mono_ae integrable_condExp (integrable_const N) (hb 0 (Nat.zero_le n))
    rw [integral_condExp (F.le 0)] at hb0
    change (∫ ω, C n ω - C 0 ω ∂P) ≤ ∫ _ : Ω, N ∂P at hb0
    rw [integral_sub (hi n) (hi 0)] at hb0
    have hzero : (∫ ω, C 0 ω ∂P) = 0 := by
      simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae h0
    simpa only [hzero, sub_zero, integral_const, probReal_univ, one_smul] using hb0
  have hprod (k : ℕ) : Integrable (fun ω ↦ (C n ω - C k ω) * (C (k + 1) ω - C k ω)) P :=
    ((hL n).sub (hL k)).integrable_mul ((hL (k + 1)).sub (hL k))
  have hterm (k : ℕ) (hk : k ∈ range n) :
      (∫ ω, (C n ω - C k ω) * (C (k + 1) ω - C k ω) ∂P) ≤
        N * ∫ ω, C (k + 1) ω - C k ω ∂P := by
    have hsm := (hp.measurable_add_one k).sub (hp.stronglyAdapted k)
    have hpull := condExp_mul_of_stronglyMeasurable_right hsm (hprod k) ((hi n).sub (hi k))
    have hce : Integrable
        (fun ω ↦ P[C n - C k | F k] ω * (C (k + 1) ω - C k ω)) P :=
      integrable_condExp.congr hpull
    calc
      _ = ∫ ω, P[C n - C k | F k] ω * (C (k + 1) ω - C k ω) ∂P := by
        rw [← integral_condExp (F.le k)]
        exact integral_congr_ae hpull
      _ ≤ ∫ ω, N * (C (k + 1) ω - C k ω) ∂P := by
        apply integral_mono_ae hce (((hi (k + 1)).sub (hi k)).const_mul N)
        filter_upwards [hb k (Nat.le_of_lt (mem_range.mp hk)), hm] with ω hω hmω
        exact mul_le_mul_of_nonneg_right hω (sub_nonneg.mpr (hmω k.le_succ))
      _ = _ := integral_const_mul _ _
  have hsum : Integrable
      (fun ω ↦ ∑ k ∈ range n, (C n ω - C k ω) * (C (k + 1) ω - C k ω)) P :=
    integrable_finsetSum _ (fun k _ ↦ hprod k)
  have hpoint : ∀ᵐ ω ∂P, C n ω ^ 2 ≤
      2 * ∑ k ∈ range n, (C n ω - C k ω) * (C (k + 1) ω - C k ω) := by
    filter_upwards [h0] with ω hω
    simpa only [hω, Pi.zero_apply, sub_zero] using sq_sub_le_twice_sum_remaining (C · ω) n
  calc
    _ ≤ ∫ ω, 2 * ∑ k ∈ range n, (C n ω - C k ω) * (C (k + 1) ω - C k ω) ∂P :=
      integral_mono_ae (hL n).integrable_sq (hsum.const_mul 2) hpoint
    _ = 2 * ∑ k ∈ range n,
        ∫ ω, (C n ω - C k ω) * (C (k + 1) ω - C k ω) ∂P := by
      rw [integral_const_mul, integral_finsetSum _ (fun k _ ↦ hprod k)]
    _ ≤ 2 * ∑ k ∈ range n, N * ∫ ω, C (k + 1) ω - C k ω ∂P :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by norm_num)
    _ = 2 * N * ∫ ω, C n ω ∂P := by
      simp_rw [integral_sub (hi _) (hi _)]
      rw [← mul_sum, sum_range_sub (fun k ↦ ∫ ω, C k ω ∂P) n]
      have hzero : (∫ ω, C 0 ω ∂P) = 0 := by
        simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae h0
      rw [hzero, sub_zero, mul_assoc]
    _ ≤ 2 * N ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hE hN]

end MeasureTheory
