/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Algebra
public import StochLean.Probability.Process.Path.UniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Real path series with finitely many active terms on compact horizons

Uniform finite support on each finite horizon makes the original real series
genuinely summable at every time. Its partial sums eventually equal it on
each compact horizon, hence converge locally uniformly. Monotonicity and
cadlag regularity are inherited from the individual real paths.

No summable bound on the whole half-line is assumed. The finite cutoff may
depend on the horizon and, when this pathwise result is used for a process,
on its sample point. No alternative series or path version is selected.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {X : ℕ → ℝ≥0 → ℝ}

/-- Compact-horizon finite support proves actual summability and local
uniform convergence of the ordinary partial sums to the ordinary series. -/
theorem summable_tendstoUniformlyOn_tsum_of_locally_finite
    (hz : ∀ T : ℝ≥0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ t, t ≤ T → X n t = 0) :
    (∀ t, Summable (fun n ↦ X n t)) ∧
      ∀ T, TendstoUniformlyOn
        (fun (N : ℕ) t ↦ ∑ n ∈ Finset.range N, X n t)
        (fun t ↦ ∑' n, X n t) atTop (Icc 0 T) := by
  constructor
  · intro t
    obtain ⟨N, hN⟩ := hz t
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    exact hN n (Nat.le_of_not_gt (fun h ↦ hn (Finset.mem_range.mpr h))) t le_rfl
  · intro T
    obtain ⟨N, hN⟩ := hz T
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [eventually_ge_atTop N] with K hK t ht
    have he : (∑' n, X n t) = ∑ n ∈ Finset.range K, X n t := by
      apply tsum_eq_sum
      intro n hn
      exact hN n (hK.trans (Nat.le_of_not_gt
        (fun h ↦ hn (Finset.mem_range.mpr h)))) t ht.2
    rw [he, dist_self]
    exact hε

/-- Monotone cadlag summands with uniformly finite support on every finite
horizon have a monotone cadlag actual series. No positivity assumption on
the individual summands or global summability hypothesis is needed. -/
theorem monotone_isCadlagPath_tsum_of_locally_finite
    (hz : ∀ T : ℝ≥0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ t, t ≤ T → X n t = 0)
    (hm : ∀ n, Monotone (X n)) (hc : ∀ n, IsCadlagPath (X n)) :
    Monotone (fun t ↦ ∑' n, X n t) ∧ IsCadlagPath (fun t ↦ ∑' n, X n t) := by
  constructor
  · intro s t hst
    obtain ⟨N, hN⟩ := hz t
    have he (u : ℝ≥0) (hu : u ≤ t) :
        (∑' n, X n u) = ∑ n ∈ Finset.range N, X n u := by
      apply tsum_eq_sum
      intro n hn
      exact hN n (Nat.le_of_not_gt (fun h ↦ hn (Finset.mem_range.mpr h))) u hu
    change (∑' n, X n s) ≤ ∑' n, X n t
    rw [he s hst, he t le_rfl]
    exact Finset.sum_le_sum (fun n _ ↦ hm n hst)
  · exact isCadlagPath_of_locallyUniform
      (fun N ↦ IsCadlagPath.finset_sum (Finset.range N) X (fun n _ ↦ hc n))
      (summable_tendstoUniformlyOn_tsum_of_locally_finite hz).2

end ProbabilityTheory
