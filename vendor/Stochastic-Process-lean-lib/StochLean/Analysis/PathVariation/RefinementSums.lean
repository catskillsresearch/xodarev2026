/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TotalVariation

/-! # Subadditive cell sums under finite partition refinement

Only the actual finite endpoint set of the fine partition is used in the
triangle hypothesis. Repeated endpoints are allowed. Prefix sums along that
same partition control each coarse cell and then telescope.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

/-- A nonnegative cell cost with the ordered triangle inequality increases
under refinement. The triangle property is needed only on fine endpoints. -/
theorem Refines.sum_cells_le {ρ π : TimePartition T} (h : ρ.Refines π)
    (w : ℝ≥0 → ℝ≥0 → ℝ) (hzero : ∀ t, w t t = 0)
    (hn : ∀ s ∈ Set.range ρ.point, ∀ t ∈ Set.range ρ.point, s ≤ t → 0 ≤ w s t)
    (htri : ∀ a ∈ Set.range ρ.point, ∀ b ∈ Set.range ρ.point,
      ∀ c ∈ Set.range ρ.point, a ≤ b → b ≤ c → w a c ≤ w a b + w b c) :
    (∑ i, w (π.left i) (π.right i)) ≤ ∑ j, w (ρ.left j) (ρ.right j) := by
  classical
  let v (k : ℕ) := w (ρ.pointNat k) (ρ.pointNat (k + 1))
  let S (k : ℕ) := ∑ j ∈ Finset.range k, v j
  have hchain (a b : ℕ) (hab : a ≤ b) :
      w (ρ.pointNat a) (ρ.pointNat b) ≤ ∑ k ∈ Finset.Ico a b, v k := by
    induction b, hab using Nat.le_induction with
    | base => simp [hzero]
    | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab]
      exact (htri _ (ρ.pointNat_mem a) _ (ρ.pointNat_mem b) _
        (ρ.pointNat_mem (b + 1)) (ρ.pointNat_mono hab)
        (ρ.pointNat_mono (Nat.le_succ b))).trans (add_le_add ih (le_refl _))
  have hre (t : ℝ≥0) (ht : t ∈ Set.range ρ.point) :
      ρ.pointNat (ρ.ceilingIndex t) = t := by
    obtain ⟨i, rfl⟩ := ht
    rw [ρ.pointNat_fin]
    apply le_antisymm
    · exact ρ.monotone_point (ρ.ceilingIndex_le (min_le_left _ _))
    · simpa only [min_eq_left (ρ.point_le_horizon i), ceilingPoint] using
        ρ.min_le_ceilingPoint (ρ.point i)
  let q (t : ℝ≥0) := S (ρ.ceilingIndex t).val
  have hcell (i : Fin π.size) : w (π.left i) (π.right i) ≤
      π.increment q i := by
    have hl := h (show π.left i ∈ Set.range π.point from ⟨i.castSucc, rfl⟩)
    have hr := h (show π.right i ∈ Set.range π.point from ⟨i.succ, rfl⟩)
    have hle : (ρ.ceilingIndex (π.left i)).val ≤ (ρ.ceilingIndex (π.right i)).val :=
      ρ.ceilingIndex_mono (π.left_le_right i)
    have hh := hchain _ _ hle
    rw [hre _ hl, hre _ hr, Finset.sum_Ico_eq_sub _ hle] at hh
    exact hh
  have hzeroIndex : ρ.ceilingIndex 0 = 0 := by
    apply le_antisymm
    · apply ρ.ceilingIndex_le
      simp [ρ.first_eq_zero]
    · exact bot_le
  have hqzero : q 0 = 0 := by simp [q, S, hzeroIndex]
  have hqT : q T ≤ ∑ j, w (ρ.left j) (ρ.right j) := by
    calc
      q T ≤ S ρ.size := by
        apply sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.le_of_lt_succ (ρ.ceilingIndex T).isLt))
        intro k _ _
        exact hn _ (ρ.pointNat_mem k) _ (ρ.pointNat_mem (k + 1))
          (ρ.pointNat_mono (Nat.le_succ k))
      _ = ∑ j, w (ρ.left j) (ρ.right j) := by
        change (∑ k ∈ Finset.range ρ.size, v k) = _
        rw [Finset.sum_range]
        apply sum_congr rfl
        intro i _
        have hl := ρ.pointNat_fin i.castSucc
        have hr := ρ.pointNat_fin i.succ
        simpa only [v, left, right, Fin.val_castSucc, Fin.val_succ] using congrArg₂ w hl hr
  calc
    (∑ i, w (π.left i) (π.right i)) ≤ ∑ i, π.increment q i :=
      sum_le_sum fun i _ ↦ hcell i
    _ = q T := by rw [π.sum_increment, hqzero, sub_zero]
    _ ≤ _ := hqT

end StochLean.TimePartition
