/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real

/-! # Vector increment energies bounded by the existing coordinate square sums

These are deterministic finite sums, not a new stochastic bracket. The finite
product uses Mathlib's sup norm; domination by coordinate squares also covers
the empty coordinate type.
-/

@[expose] public section

open Finset Filter
open scoped NNReal

namespace StochLean

theorem norm_sq_pi_le_sum_sq {ι : Type*} [Fintype ι] (z : ι → ℝ) :
    ‖z‖ ^ 2 ≤ ∑ i, (z i) ^ 2 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have hz : z = 0 := by ext i; exact isEmptyElim i
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply, sum_const_zero, le_refl]
  | inr h =>
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm z).1
    rw [← hi]
    change ‖z i‖ ^ 2 ≤ _
    rw [Real.norm_eq_abs, sq_abs]
    exact single_le_sum (fun j _ ↦ sq_nonneg (z j)) (mem_univ i)

noncomputable def normSquareVariationSum {E : Type*} [NormedAddCommGroup E]
    {T : ℝ≥0} (π : TimePartition T) (x : ℝ≥0 → E) : ℝ :=
  ∑ i : Fin π.size, ‖x (π.right i) - x (π.left i)‖ ^ 2

theorem normSquareVariationSum_nonneg {E : Type*} [NormedAddCommGroup E]
    {T : ℝ≥0} (π : TimePartition T) (x : ℝ≥0 → E) : 0 ≤ normSquareVariationSum π x :=
  sum_nonneg fun _ _ ↦ sq_nonneg _

theorem normSquareVariationSum_pi_le {ι : Type*} [Fintype ι]
    {T : ℝ≥0} (π : TimePartition T) (x : ℝ≥0 → ι → ℝ) :
    normSquareVariationSum π x ≤ ∑ j, quadraticVariationSum π (fun t ↦ x t j) := by
  calc
    _ ≤ ∑ i : Fin π.size, ∑ j, (x (π.right i) j - x (π.left i) j) ^ 2 :=
      sum_le_sum (fun i _ ↦ norm_sq_pi_le_sum_sq (x (π.right i) - x (π.left i)))
    _ = _ := by rw [sum_comm]; rfl

theorem summable_norm_sq_pi_of_summable_sq {ι α : Type*} [Fintype ι]
    (z : α → ι → ℝ) (hz : ∀ i, Summable (fun a ↦ (z a i) ^ 2)) :
    Summable (fun a ↦ ‖z a‖ ^ 2) := by
  have hs : Summable (fun a ↦ ∑ i, (z a i) ^ 2) := summable_sum (fun i _ ↦ hz i)
  apply hs.of_norm_bounded
  intro a
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z a‖)] using norm_sq_pi_le_sum_sq (z a)

end StochLean
