/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic

/-! # Extending and shifting actual finite time partitions

Both constructions stay in the existing `TimePartition` type. An appended
terminal cell or prepended initial cell is retained even when its length is
zero. Consequently the exact cell-sum identities need no vanishing-diagonal
assumption on the cost function.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

variable {H K : ℝ≥0}

/-- Append the actual new terminal point, retaining all old endpoints and
the new cell even when the old and new horizons coincide. -/
theorem exists_extend_horizon (π : TimePartition H) (hHK : H ≤ K) :
    ∃ ρ : TimePartition K, Set.range ρ.point = Set.range π.point ∪ {K} ∧
      ∀ w : ℝ≥0 → ℝ≥0 → ℝ,
        (∑ i, w (ρ.left i) (ρ.right i)) =
          (∑ i, w (π.left i) (π.right i)) + w H K := by
  let p : Fin (π.size + 1 + 1) → ℝ≥0 := Fin.snoc π.point K
  have hl (i : Fin π.size) : p i.castSucc.castSucc = π.left i := by
    simp only [p, Fin.snoc_castSucc, left]
  have hr (i : Fin π.size) : p i.castSucc.succ = π.right i := by
    rw [← Fin.castSucc_succ]
    simp only [p, Fin.snoc_castSucc, right]
  have hlastl : p (Fin.last π.size).castSucc = H := by
    simp only [p, Fin.snoc_castSucc, π.last_eq_horizon]
  have hlastr : p (Fin.last π.size).succ = K := by simp [p]
  have hm : Monotone p := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    cases i using Fin.lastCases with
    | cast i => simpa only [hl, hr] using π.left_le_right i
    | last => simpa only [hlastl, hlastr] using hHK
  let ρ : TimePartition K :=
    { size := π.size + 1
      point := p
      monotone_point := hm
      first_eq_zero := by simp [p, π.first_eq_zero]
      last_eq_horizon := by simp [p] }
  refine ⟨ρ, ?_, fun w ↦ ?_⟩
  · change Set.range (Fin.snoc π.point K) = _
    rw [Fin.range_snoc]
    ext t
    simp only [mem_insert_iff, mem_union, mem_singleton_iff, or_comm]
  · change (∑ i : Fin (π.size + 1), w (p i.castSucc) (p i.succ)) = _
    rw [Fin.sum_univ_castSucc]
    simp only [hl, hr, hlastl, hlastr]

/-- Shift all original endpoints by `t` and prepend the actual initial
point zero. The new first cell is present also when `t = 0`. -/
theorem exists_prepend_shift (π : TimePartition H) (t : ℝ≥0) :
    ∃ ρ : TimePartition (t + H),
      Set.range ρ.point = {0} ∪ (fun s : ℝ≥0 ↦ t + s) '' Set.range π.point ∧
      ∀ w : ℝ≥0 → ℝ≥0 → ℝ,
        (∑ i, w (ρ.left i) (ρ.right i)) =
          w 0 t + ∑ i, w (t + π.left i) (t + π.right i) := by
  let p : Fin (π.size + 1 + 1) → ℝ≥0 := Fin.cons 0 (fun i ↦ t + π.point i)
  have hl (i : Fin π.size) : p i.succ.castSucc = t + π.left i := by
    simp only [p, Fin.castSucc_succ, Fin.cons_succ, left]
  have hr (i : Fin π.size) : p i.succ.succ = t + π.right i := by
    simp only [p, Fin.cons_succ, right]
  have hfirstl : p (0 : Fin (π.size + 1)).castSucc = 0 := by simp [p]
  have hfirstr : p (0 : Fin (π.size + 1)).succ = t := by
    simp only [p, Fin.cons_succ, π.first_eq_zero, add_zero]
  have hm : Monotone p := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    cases i using Fin.cases with
    | zero => simpa only [hfirstl, hfirstr] using (show 0 ≤ t from bot_le)
    | succ i =>
      simpa only [hl, hr] using add_le_add (le_refl t) (π.left_le_right i)
  let ρ : TimePartition (t + H) :=
    { size := π.size + 1
      point := p
      monotone_point := hm
      first_eq_zero := by simp [p]
      last_eq_horizon := by simp [p, π.last_eq_horizon] }
  refine ⟨ρ, ?_, fun w ↦ ?_⟩
  · change Set.range (Fin.cons 0 (fun i ↦ t + π.point i)) = _
    rw [Fin.range_cons]
    ext u
    simp only [mem_insert_iff, mem_union, mem_singleton_iff, Set.mem_range, Set.mem_image]
    constructor
    · rintro (hu | ⟨i, hi⟩)
      · exact Or.inl hu
      · exact Or.inr ⟨π.point i, ⟨i, rfl⟩, hi⟩
    · rintro (hu | ⟨s, ⟨i, rfl⟩, hi⟩)
      · exact Or.inl hu
      · exact Or.inr ⟨i, hi⟩
  · change (∑ i : Fin (π.size + 1), w (p i.castSucc) (p i.succ)) = _
    rw [Fin.sum_univ_succ]
    simp only [hl, hr, hfirstl, hfirstr]

end StochLean.TimePartition
