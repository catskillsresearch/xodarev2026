/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic

/-! # Absolute summability of mixed products and square-sum polarization -/

@[expose] public section

namespace StochLean

variable {ι : Type*} {a b : ι → ℝ}

theorem summable_mul_of_summable_sq (ha : Summable (fun i ↦ (a i) ^ 2))
    (hb : Summable (fun i ↦ (b i) ^ 2)) : Summable (fun i ↦ a i * b i) := by
  apply (ha.add hb).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a i - b i), sq_nonneg (a i + b i)]

theorem summable_abs_mul_of_summable_sq (ha : Summable (fun i ↦ (a i) ^ 2))
    (hb : Summable (fun i ↦ (b i) ^ 2)) : Summable (fun i ↦ |a i * b i|) := by
  apply (ha.add hb).of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a i - b i), sq_nonneg (a i + b i)]

theorem tsum_sq_add_of_summable_sq (ha : Summable (fun i ↦ (a i) ^ 2))
    (hb : Summable (fun i ↦ (b i) ^ 2)) :
    (∑' i, (a i + b i) ^ 2) = (∑' i, (a i) ^ 2) +
      2 * (∑' i, a i * b i) + (∑' i, (b i) ^ 2) := by
  have hab := summable_mul_of_summable_sq ha hb
  have heq : (fun i ↦ (a i + b i) ^ 2) =
      (fun i ↦ (a i) ^ 2 + 2 * (a i * b i) + (b i) ^ 2) := by
    funext i
    ring
  rw [heq, (ha.add (hab.mul_left 2)).tsum_add hb, ha.tsum_add (hab.mul_left 2),
    hab.tsum_mul_left 2]

end StochLean
