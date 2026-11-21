/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith

/-! # A real affine function nonnegative at every integer has zero slope -/

@[expose] public section

namespace StochLean

theorem eq_zero_of_forall_int_affine_nonneg {a b : ℝ}
    (h : ∀ n : ℤ, 0 ≤ a + (n : ℝ) * b) : b = 0 := by
  by_contra hb
  rcases lt_or_gt_of_ne hb with hn | hp
  · obtain ⟨n, hlt⟩ := exists_int_gt (-a / b)
    have hm : (n : ℝ) * b < -a := (div_lt_iff_of_neg hn).mp hlt
    linarith [h n]
  · obtain ⟨n, hlt⟩ := exists_int_lt (-a / b)
    have hm : (n : ℝ) * b < -a := (lt_div_iff₀ hp).mp hlt
    linarith [h n]

end StochLean
