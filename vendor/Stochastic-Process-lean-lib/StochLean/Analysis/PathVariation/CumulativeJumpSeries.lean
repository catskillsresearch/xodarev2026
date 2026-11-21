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

/-! # Local finite variation of actual absolutely summable jump series

Positive and negative cumulative series are monotone. Their difference
is the original series, so no enumeration of its countable support or
expected-variation bound is needed.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean

theorem monotone_tsum_Ioc_of_nonneg {g : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ g s)) (hg : ∀ s, 0 ≤ g s) :
    Monotone (fun T : ℝ≥0 ↦ ∑' s : Ioc 0 T, g s) := by
  intro t u htu
  let hsub : Ioc (0 : ℝ≥0) t ⊆ Ioc 0 u := fun _ hs ↦ ⟨hs.1, hs.2.trans htu⟩
  exact (hs t).tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub)
    (fun s _ ↦ hg s) (fun _ ↦ le_rfl) (hs u)

theorem locallyBoundedVariationOn_tsum_Ioc {g : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |g s|)) :
    LocallyBoundedVariationOn (fun T : ℝ≥0 ↦ ∑' s : Ioc 0 T, g s) univ := by
  let p : ℝ≥0 → ℝ := fun s ↦ (|g s| + g s) / 2
  let n : ℝ≥0 → ℝ := fun s ↦ (|g s| - g s) / 2
  have hp (T : ℝ≥0) : Summable (fun s : Ioc 0 T ↦ p s) :=
    ((hs T).add (hs T).of_abs).div_const 2
  have hn (T : ℝ≥0) : Summable (fun s : Ioc 0 T ↦ n s) :=
    ((hs T).sub (hs T).of_abs).div_const 2
  have hp0 (s : ℝ≥0) : 0 ≤ p s := by
    have h := neg_abs_le (g s)
    dsimp only [p]
    linarith only [h]
  have hn0 (s : ℝ≥0) : 0 ≤ n s := by
    have h := le_abs_self (g s)
    dsimp only [n]
    linarith only [h]
  have hpm := monotone_tsum_Ioc_of_nonneg (g := p) hp hp0
  have hnm := monotone_tsum_Ioc_of_nonneg (g := n) hn hn0
  have hv := locallyBoundedVariationOn_sub (hpm.monotoneOn univ).locallyBoundedVariationOn
    (hnm.monotoneOn univ).locallyBoundedVariationOn
  have heq : (fun T : ℝ≥0 ↦ (∑' s : Ioc 0 T, p s) - ∑' s : Ioc 0 T, n s) =
      fun T : ℝ≥0 ↦ ∑' s : Ioc 0 T, g s := by
    funext T
    rw [← (hp T).tsum_sub (hn T)]
    apply tsum_congr
    intro s
    dsimp only [p, n]
    ring
  rwa [heq] at hv

end StochLean
