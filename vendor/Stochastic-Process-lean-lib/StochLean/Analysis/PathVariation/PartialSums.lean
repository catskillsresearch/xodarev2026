/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CompletedSums

/-!
# The last partial cell has uniformly vanishing error

All partitions have the same enclosing horizon. Stopping a deterministic path
at an earlier time gives its usual partial square/cross sum; the difference
from completed-cell sums is confined to at most one cell. Continuity and
vanishing mesh make this difference uniformly small over the entire horizon.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

variable {T : ℝ≥0}

theorem TimePartition.right_le_left_of_lt (π : TimePartition T) {i j : Fin π.size}
    (hij : i < j) : π.right i ≤ π.left j :=
  π.monotone_point (show i.succ ≤ j.castSucc from hij)

theorem TimePartition.crossingCells_subsingleton (π : TimePartition T) (s : ℝ≥0) :
    {i : Fin π.size | π.left i < s ∧ s < π.right i}.Subsingleton := by
  intro i hi j hj
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim ((not_lt_of_ge (π.right_le_left_of_lt hij)) (hj.1.trans hi.2))
  · exact hij
  · exact False.elim ((not_lt_of_ge (π.right_le_left_of_lt hji)) (hi.1.trans hj.2))

/-- Exact last-cell identity, including endpoints and zero-length cells. -/
theorem covariationSum_stop_sub_completed (π : TimePartition T) (f g : ℝ≥0 → ℝ)
    (s : ℝ≥0) :
    covariationSum π (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) -
      completedCovariationSum π f g s =
        ∑ i, if π.left i < s ∧ s < π.right i then
          (f s - f (π.left i)) * (g s - g (π.left i)) else 0 := by
  classical
  rw [covariationSum, completedCovariationSum, cumulativeStepSum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hr : π.right i ≤ s
  · have hl := (π.left_le_right i).trans hr
    simp [TimePartition.increment, hr, hl, not_lt_of_ge hr]
  · have hsr := lt_of_not_ge hr
    by_cases hl : π.left i < s
    · simp [TimePartition.increment, hr, hl, hsr, min_eq_right hsr.le, min_eq_left hl.le]
    · have hsl := le_of_not_gt hl
      simp [TimePartition.increment, hr, hl, min_eq_right hsr.le, min_eq_right hsl]

theorem abs_covariationSum_stop_sub_completed_le (π : TimePartition T)
    (f g : ℝ≥0 → ℝ) (s : ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ i, π.left i < s → s < π.right i → |f s - f (π.left i)| ≤ a)
    (hg : ∀ i, π.left i < s → s < π.right i → |g s - g (π.left i)| ≤ b) :
    |covariationSum π (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) -
      completedCovariationSum π f g s| ≤ a * b := by
  classical
  let A := univ.filter fun i ↦ π.left i < s ∧ s < π.right i
  have hcard : A.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact π.crossingCells_subsingleton s (mem_filter.mp hi).2 (mem_filter.mp hj).2
  rw [covariationSum_stop_sub_completed, ← sum_filter]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i ∈ A, |(f s - f (π.left i)) * (g s - g (π.left i))|) ≤ A.card • (a * b) := by
      apply sum_le_card_nsmul
      intro i hi
      obtain ⟨hl, hr⟩ := (mem_filter.mp hi).2
      rw [abs_mul]
      exact mul_le_mul (hf i hl hr) (hg i hl hr) (abs_nonneg _) ha
    _ ≤ a * b := by
      rw [nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right (show (A.card : ℝ) ≤ 1 by exact_mod_cast hcard)
        (mul_nonneg ha hb)).trans_eq (one_mul _)

/-- Uniform in the partial terminal time, not merely convergence at each fixed time. -/
theorem eventually_uniform_abs_partialCovariation_error_lt
    {π : ℕ → TimePartition T} {f g : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ≤ T,
      |covariationSum (π n) (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) -
        completedCovariationSum (π n) f g s| < ε := by
  have huf := isCompact_Icc.uniformContinuousOn_of_continuous hf
  have hug := isCompact_Icc.uniformContinuousOn_of_continuous hg
  obtain ⟨ηf, hηf, hmodf⟩ := Metric.uniformContinuousOn_iff.mp huf (ε / 2) (by positivity)
  obtain ⟨ηg, hηg, hmodg⟩ := Metric.uniformContinuousOn_iff.mp hug 1 zero_lt_one
  filter_upwards [hmesh.eventually_lt_const (lt_min hηf hηg)] with n hn
  intro s hs
  have hdist (i : Fin (π n).size) (hl : (π n).left i < s) (hr : s < (π n).right i) :
      dist s ((π n).left i) ≤ ((π n).mesh : ℝ) := by
    calc
      dist s ((π n).left i) ≤ dist ((π n).right i) ((π n).left i) := by
        rw [NNReal.dist_eq, NNReal.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hl.le)),
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (π n).left_le_right i))]
        exact sub_le_sub_right (by exact_mod_cast hr.le) _
      _ = ((π n).gap i : ℝ) := (π n).dist_right_left_eq_gap i
      _ ≤ (π n).mesh := by exact_mod_cast (π n).gap_le_mesh i
  have hb := abs_covariationSum_stop_sub_completed_le (π n) f g s
    (a := ε / 2) (b := 1) (by positivity) zero_le_one
    (fun i hl hr ↦ (hmodf s ⟨bot_le, hs⟩ ((π n).left i)
      ⟨bot_le, (π n).point_le_horizon _⟩
      ((hdist i hl hr).trans_lt (hn.trans_le (min_le_left _ _)))).le)
    (fun i hl hr ↦ (hmodg s ⟨bot_le, hs⟩ ((π n).left i)
      ⟨bot_le, (π n).point_le_horizon _⟩
      ((hdist i hl hr).trans_lt (hn.trans_le (min_le_right _ _)))).le)
  exact hb.trans_lt (by linarith)

theorem tendsto_partialCovariation_error_zero {π : ℕ → TimePartition T}
    {f g : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) {s : ℝ≥0} (hs : s ≤ T) :
    Tendsto (fun n ↦ covariationSum (π n) (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) -
      completedCovariationSum (π n) f g s) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ ↦ ha.trans_le (norm_nonneg _)
  · intro ε hε
    filter_upwards [eventually_uniform_abs_partialCovariation_error_lt hf hg hmesh hε] with n hn
    simpa only [sub_zero, Real.norm_eq_abs] using hn s hs

theorem tendsto_completedCovariationSum_of_partial {π : ℕ → TimePartition T}
    {f g : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) {s : ℝ≥0} (hs : s ≤ T)
    {c : ℝ} (hc : HasCovariationAlong π (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) c) :
    Tendsto (fun n ↦ completedCovariationSum (π n) f g s) atTop (𝓝 c) := by
  simpa only [sub_sub_cancel, sub_zero] using hc.sub
    (tendsto_partialCovariation_error_zero hf hg hmesh hs)

end StochLean
