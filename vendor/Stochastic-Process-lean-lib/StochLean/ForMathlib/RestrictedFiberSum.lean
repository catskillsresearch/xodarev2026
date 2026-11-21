/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Regrouping an absolutely convergent series over selected fibers

This is the actual restricted sum, with no chosen enumeration of the
support and no injectivity requirement on the grouping map.
-/

@[expose] public section

open Set

namespace StochLean

theorem tsum_subtype_fiberwise {ι α : Type*} {w : ι → ℝ}
    (hw : Summable w) (a : ι → α) (S : Set α) :
    (∑' s : S, ∑' i : a ⁻¹' {(s : α)}, w i) = ∑' i, (a ⁻¹' S).indicator w i := by
  classical
  have hf := (hw.indicator (a ⁻¹' S)).hasSum.tsum_fiberwise a
  rw [tsum_subtype S (fun s ↦ ∑' i : a ⁻¹' {s}, w i)]
  rw [← hf.tsum_eq]
  apply tsum_congr
  intro s
  by_cases hs : s ∈ S
  · rw [indicator_of_mem hs]
    apply tsum_congr
    intro i
    have hi : a i = s := i.2
    exact (indicator_of_mem (show (i : ι) ∈ a ⁻¹' S by simpa only [mem_preimage, hi]
      using hs) w).symm
  · rw [indicator_of_notMem hs]
    symm
    calc
      _ = ∑' i : a ⁻¹' {s}, (0 : ℝ) := by
        apply tsum_congr
        intro i
        have hi : a i = s := i.2
        exact indicator_of_notMem (show (i : ι) ∉ a ⁻¹' S by
          simpa only [mem_preimage, hi] using hs) w
      _ = 0 := tsum_zero

end StochLean
