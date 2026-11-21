/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Approximation

/-! # Exact endpoint and order properties of the existing ceiling projection -/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem ceilingPoint_eq_of_mem (π : TimePartition T) {s : ℝ≥0}
    (hs : s ∈ Set.range π.point) : π.ceilingPoint s = s := by
  obtain ⟨i, rfl⟩ := hs
  apply le_antisymm
  · exact π.monotone_point (π.ceilingIndex_le (min_le_left _ _))
  · simpa only [min_eq_left (π.point_le_horizon i)] using π.min_le_ceilingPoint (π.point i)

theorem pointNat_ceilingIndex_eq_of_mem (π : TimePartition T) {s : ℝ≥0}
    (hs : s ∈ Set.range π.point) : π.pointNat (π.ceilingIndex s).val = s :=
  (π.pointNat_fin (π.ceilingIndex s)).trans (π.ceilingPoint_eq_of_mem hs)

theorem ceilingIndex_le_iff (π : TimePartition T) {s : ℝ≥0} (hs : s ≤ T) (k : ℕ) :
    (π.ceilingIndex s).val ≤ k ↔ s ≤ π.pointNat k := by
  constructor
  · intro h
    have hi : (π.ceilingIndex s).val ≤ min k π.size :=
      le_min h (Nat.le_of_lt_succ (π.ceilingIndex s).isLt)
    have hmin : s ≤ π.ceilingPoint s := by
      simpa only [min_eq_left hs] using π.min_le_ceilingPoint s
    exact hmin.trans (π.monotone_point hi)
  · intro h
    have hi := π.ceilingIndex_le (i := ⟨min k π.size, Nat.lt_succ_of_le (min_le_right _ _)⟩)
      ((min_le_left s T).trans h)
    exact (show (π.ceilingIndex s).val ≤ min k π.size from hi).trans (min_le_left _ _)

end StochLean.TimePartition
