/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.SingleJump
public import StochLean.Probability.Process.Path.Algebra
public import StochLean.Probability.Process.Path.UniformLimit
public import StochLean.ForMathlib.VariationAlgebra
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Absolutely summable steps at finite or infinite lifetimes

The actual sum of closed lifetime steps converges uniformly on the entire
half-line, has cadlag paths, and has whole-half-line variation bounded by the
sum of the coefficient norms. Lifetimes may coincide, be zero, or be infinite.
No arbitrary finite replacement of an infinite lifetime is used: its step is
zero at every finite time. The sum is the ordinary existing `tsum` expression,
and its convergence is proved from absolute summability.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (τ : ℕ → WithTop ℝ≥0) {K : ℕ → ℝ}

/-- Absolute coefficient summability gives uniform convergence on all finite
times simultaneously, not just on each compact interval. -/
theorem tendstoUniformly_tsum_indicator_lifetime_le
    (hK : Summable (fun n ↦ ‖K n‖)) :
    TendstoUniformly
      (fun (N : ℕ) (t : ℝ≥0) ↦
        ∑ n ∈ Finset.range N, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0)
      (fun t : ℝ≥0 ↦ ∑' n, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) atTop := by
  apply tendstoUniformly_tsum_nat hK
  intro n t
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (K n)

/-- The genuine absolutely convergent lifetime-step series is cadlag,
including the initial time and infinite lifetimes. -/
theorem isCadlagPath_tsum_indicator_lifetime_le
    (hK : Summable (fun n ↦ ‖K n‖)) :
    IsCadlagPath
      (fun t : ℝ≥0 ↦ ∑' n, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) := by
  apply isCadlagPath_of_locallyUniform
    (x := fun N t ↦ ∑ n ∈ Finset.range N,
      if τ n ≤ (t : WithTop ℝ≥0) then K n else 0)
  · intro N
    apply IsCadlagPath.finset_sum
    intro n _
    simpa only [indicator_apply, mem_ofPred_eq] using
      isCadlagPath_indicator_lifetime_le (fun _ : Unit ↦ τ n) (fun _ ↦ K n) ()
  · intro T
    exact (tendstoUniformly_tsum_indicator_lifetime_le τ hK).tendstoUniformlyOn

private theorem eVariationOn_finset_indicator_lifetime_le (s : Finset ℕ) :
    eVariationOn
      (fun t : ℝ≥0 ↦ ∑ n ∈ s, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
        ENNReal.ofReal (∑ n ∈ s, ‖K n‖) := by
  classical
  have hstep (n : ℕ) :
      eVariationOn (fun t : ℝ≥0 ↦ if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
        ENNReal.ofReal ‖K n‖ := by
    have he := eVariationOn_univ_indicator_lifetime_le
      (fun _ : Unit ↦ τ n) (fun _ ↦ K n) ()
    simp only [indicator_apply, mem_ofPred_eq] at he
    rw [he]
    split_ifs
    · exact le_rfl
    · exact bot_le
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, ENNReal.ofReal_zero]
    exact ((eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self 0).le
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    calc
      _ ≤ eVariationOn
          (fun t : ℝ≥0 ↦ if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ +
          eVariationOn
            (fun t : ℝ≥0 ↦ ∑ i ∈ s, if τ i ≤ (t : WithTop ℝ≥0) then K i else 0) univ :=
        StochLean.eVariationOn_add_le _ _ _
      _ ≤ ENNReal.ofReal ‖K n‖ + ENNReal.ofReal (∑ i ∈ s, ‖K i‖) :=
        add_le_add (hstep n) ih
      _ = ENNReal.ofReal (‖K n‖ + ∑ i ∈ s, ‖K i‖) :=
        (ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).symm

/-- The actual infinite series has finite total variation controlled by its
absolutely summable coefficients. Finiteness is an extended-real conclusion. -/
theorem eVariationOn_univ_tsum_indicator_lifetime_le
    (hK : Summable (fun n ↦ ‖K n‖)) :
    eVariationOn
      (fun t : ℝ≥0 ↦ ∑' n, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
        ENNReal.ofReal (∑' n, ‖K n‖) := by
  have hu := tendstoUniformly_tsum_indicator_lifetime_le τ hK
  have hb (N : ℕ) :
      eVariationOn
        (fun t : ℝ≥0 ↦ ∑ n ∈ Finset.range N,
          if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
            ENNReal.ofReal (∑' n, ‖K n‖) :=
    (eVariationOn_finset_indicator_lifetime_le τ (Finset.range N)).trans
      (ENNReal.ofReal_le_ofReal (hK.sum_le_tsum _ (fun _ _ ↦ norm_nonneg _)))
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  have he := eVariationOn.lowerSemicontinuous_aux
    (fun t (_ : t ∈ (univ : Set ℝ≥0)) ↦ hu.tendsto_at t) hc
  obtain ⟨N, hN⟩ := he.exists
  exact hN.le.trans (hb N)

end ProbabilityTheory
