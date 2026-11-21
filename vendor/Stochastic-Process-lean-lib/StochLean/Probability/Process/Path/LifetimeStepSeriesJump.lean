/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LifetimeStepSeries
public import StochLean.Probability.Process.Path.LifetimeStepJump
public import StochLean.Probability.Process.Path.LeftLimitUniform
public import StochLean.Probability.Process.Stopping.Graph

/-! # Actual jumps and monotonicity of absolutely summable lifetime steps

Uniform convergence of the actual partial sums passes to their source jumps.
The finite jump identity then identifies the infinite jump as the sum of all
coefficients whose finite lifetimes equal the current time. Coincident jumps
are retained, and time zero uses the source initial-jump convention.

Disjoint finite graphs isolate one coefficient at a graph point. Nonnegative
coefficients make the actual sum increasing. No stopping, measurability or
predictability premise is required for these pathwise statements.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} (τ : ℕ → Ω → WithTop ℝ≥0) (K : ℕ → Ω → ℝ) {ω : Ω}

/-- Actual uniform convergence, not pointwise convergence alone, allows jumps
to pass through the absolutely summable closed-step series. -/
theorem jumpProcess_tsum_indicator_lifetime_le
    (hK : Summable (fun n ↦ ‖K n ω‖)) (t : ℝ≥0) :
    jumpProcess (fun s v ↦ ∑' n, {v | τ n v ≤ (s : WithTop ℝ≥0)}.indicator (K n) v) t ω =
      ∑' n, {v | τ n v = (t : WithTop ℝ≥0)}.indicator (K n) ω := by
  classical
  let S : ℕ → ℝ≥0 → Ω → ℝ := fun N s v ↦
    ∑ n ∈ Finset.range N, {v | τ n v ≤ (s : WithTop ℝ≥0)}.indicator (K n) v
  let A : ℝ≥0 → Ω → ℝ := fun s v ↦
    ∑' n, {v | τ n v ≤ (s : WithTop ℝ≥0)}.indicator (K n) v
  have hcS (N : ℕ) : IsCadlagPath (S N · ω) := by
    apply IsCadlagPath.finset_sum
    intro n _
    exact isCadlagPath_indicator_lifetime_le (τ n) (K n) ω
  have hcA : IsCadlagPath (A · ω) := by
    simpa only [A, indicator_apply, mem_ofPred_eq] using
      isCadlagPath_tsum_indicator_lifetime_le (fun n ↦ τ n ω) hK
  have hu : TendstoUniformly (fun N s ↦ S N s ω) (A · ω) atTop := by
    simpa only [S, A, indicator_apply, mem_ofPred_eq] using
      tendstoUniformly_tsum_indicator_lifetime_le (fun n ↦ τ n ω) hK
  have hj := tendsto_jumpProcess_of_uniformlyOn hcS hcA (hu.tendstoUniformlyOn (s := Icc 0 t))
  have hs : Summable (fun n ↦ {v | τ n v = (t : WithTop ℝ≥0)}.indicator (K n) ω) := by
    apply Summable.of_norm_bounded hK
    intro n
    exact norm_indicator_le_norm_self _ _
  have he (N : ℕ) : jumpProcess (S N) t ω =
      ∑ n ∈ Finset.range N, {v | τ n v = (t : WithTop ℝ≥0)}.indicator (K n) ω :=
    jumpProcess_finset_sum_indicator_lifetime_le (Finset.range N) τ K t ω
  exact tendsto_nhds_unique (hj.congr he) hs.hasSum.tendsto_sum_nat

/-- On disjoint finite graphs the actual series jump is exactly the indicated
coefficient. There is no graph point or coefficient contribution at infinity. -/
theorem jumpProcess_tsum_indicator_lifetime_le_of_disjoint
    (hK : Summable (fun n ↦ ‖K n ω‖))
    (hd : Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (τ n)) (stoppingTimeGraph (τ m))))
    {n : ℕ} {t : ℝ≥0} (ht : τ n ω = (t : WithTop ℝ≥0)) :
    jumpProcess (fun s v ↦ ∑' j, {v | τ j v ≤ (s : WithTop ℝ≥0)}.indicator (K j) v) t ω =
      K n ω := by
  classical
  rw [jumpProcess_tsum_indicator_lifetime_le τ K hK]
  have hzero (j : ℕ) (hjn : j ≠ n) :
      {v | τ j v = (t : WithTop ℝ≥0)}.indicator (K j) ω = 0 := by
    apply indicator_of_notMem
    intro hj
    exact Set.disjoint_left.mp (hd hjn) (show (t, ω) ∈ stoppingTimeGraph (τ j) from hj) ht
  rw [tsum_eq_single n hzero]
  exact indicator_of_mem (show ω ∈ {v | τ n v = (t : WithTop ℝ≥0)} from ht) (K n)

/-- Nonnegative absolutely summable coefficients give an actual increasing
closed-step series, even with coincident, zero or infinite lifetimes. -/
theorem monotone_tsum_indicator_lifetime_le_of_nonneg
    (hK : Summable (fun n ↦ ‖K n ω‖)) (hn : ∀ n, 0 ≤ K n ω) :
    Monotone (fun t : ℝ≥0 ↦ ∑' n, {v | τ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) := by
  have hs (t : ℝ≥0) :
      Summable (fun n ↦ {v | τ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) := by
    apply Summable.of_norm_bounded hK
    intro n
    exact norm_indicator_le_norm_self _ _
  intro s t hst
  apply (hs s).tsum_le_tsum _ (hs t)
  intro n
  by_cases hh : τ n ω ≤ (s : WithTop ℝ≥0)
  · have ht : τ n ω ≤ (t : WithTop ℝ≥0) :=
      hh.trans (WithTop.coe_le_coe.mpr hst)
    simp only [indicator_apply, mem_ofPred_eq, hh, ht, if_true, le_refl]
  · simp only [indicator_apply, mem_ofPred_eq, hh, if_false]
    split_ifs
    · exact hn n
    · exact le_rfl

end ProbabilityTheory
