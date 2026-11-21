/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.QuadraticPairSums
public import StochLean.Probability.Process.Path.CadlagBounded

/-! # Eventual bounds for actual partial square sums from a uniform limit -/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem eventually_bound_partialSquareSums_of_uniform_limit {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x Q : ℝ≥0 → ℝ} (hQ : IsCadlagPath Q)
    (hU : TendstoUniformlyOn
      (fun n t ↦ x 0 ^ 2 + quadraticVariationSum (π n) (fun u ↦ x (min u t)))
      Q atTop (Icc 0 T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T,
      quadraticVariationSum (π n) (fun u ↦ x (min u t)) ≤ B := by
  obtain ⟨C, hCpos, hC⟩ := hQ.exists_norm_bound_Icc T
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU 1 (by norm_num)] with n hn
  intro t ht
  have hd : |x 0 ^ 2 + quadraticVariationSum (π n) (fun u ↦ x (min u t)) - Q t| < 1 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hn t ht
  have hs := (le_abs_self _).trans_lt hd
  have hqt : Q t ≤ C := (le_abs_self _).trans (hC t ht)
  linarith only [hs, hqt, sq_nonneg (x 0)]

end StochLean
