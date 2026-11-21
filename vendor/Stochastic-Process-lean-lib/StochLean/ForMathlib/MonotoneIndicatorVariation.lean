/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.VariationAlgebra
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.Real

/-! # Variation of absolutely summable coefficients with nested cutoffs

An increasing family of index sets may activate each signed coefficient
at most once. Splitting its positive and negative parts gives the actual
sum as a difference of two monotone functions, without enumerating the
index type or imposing a sign on the coefficients.
-/

@[expose] public section

open Set

namespace StochLean

theorem monotone_tsum_indicator_of_nonneg {α ι : Type*} [Preorder α]
    {a : α → Set ι} (ha : Monotone a) {w : ι → ℝ}
    (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i) :
    Monotone (fun t ↦ ∑' i, (a t).indicator w i) := by
  classical
  intro s t hst
  apply (hw.indicator (a s)).tsum_le_tsum _ (hw.indicator (a t))
  intro i
  by_cases hi : i ∈ a s
  · simp only [indicator_of_mem hi, indicator_of_mem (ha hst hi)]
    exact le_rfl
  · rw [indicator_of_notMem hi]
    by_cases hit : i ∈ a t <;> simp [Set.indicator, hit, hw0]

theorem locallyBoundedVariationOn_tsum_monotone_indicator
    {α ι : Type*} [LinearOrder α] {a : α → Set ι} (ha : Monotone a)
    {w : ι → ℝ} (hw : Summable (fun i ↦ |w i|)) :
    LocallyBoundedVariationOn (fun t ↦ ∑' i, (a t).indicator w i) univ := by
  classical
  let p : ι → ℝ := fun i ↦ (|w i| + w i) / 2
  let n : ι → ℝ := fun i ↦ (|w i| - w i) / 2
  have hp : Summable p := (hw.add hw.of_abs).div_const 2
  have hn : Summable n := (hw.sub hw.of_abs).div_const 2
  have hp0 (i : ι) : 0 ≤ p i := by
    have h := neg_abs_le (w i)
    dsimp only [p]
    linarith only [h]
  have hn0 (i : ι) : 0 ≤ n i := by
    have h := le_abs_self (w i)
    dsimp only [n]
    linarith only [h]
  have hpm := monotone_tsum_indicator_of_nonneg ha hp hp0
  have hnm := monotone_tsum_indicator_of_nonneg ha hn hn0
  have hv := locallyBoundedVariationOn_sub (hpm.monotoneOn univ).locallyBoundedVariationOn
    (hnm.monotoneOn univ).locallyBoundedVariationOn
  have he : (fun t ↦ (∑' i, (a t).indicator p i) - ∑' i, (a t).indicator n i) =
      fun t ↦ ∑' i, (a t).indicator w i := by
    funext t
    rw [← (hp.indicator (a t)).tsum_sub (hn.indicator (a t))]
    apply tsum_congr
    intro i
    by_cases hi : i ∈ a t
    · simp only [indicator_of_mem hi, p, n]
      ring
    · simp only [indicator_of_notMem hi, sub_zero]
  rwa [he] at hv

end StochLean
