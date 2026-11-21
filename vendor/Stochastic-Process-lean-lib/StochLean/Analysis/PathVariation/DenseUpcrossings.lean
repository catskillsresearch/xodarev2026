/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ExpandingDyadic
public import StochLean.Analysis.PathVariation.UpcrossingRefinement

/-! # Native upcrossing counts on expanding dyadic grids

The extended count aggregates the existing finite owner. Finite counts attain
a maximum; no new crossing-time convention or endpoint enumeration is used.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace StochLean

/-- The increasing supremum of native finite upcrossing counts. -/
noncomputable def denseUpcrossings {Ω : Type*} (a b : ℝ) (X : ℝ≥0 → Ω → ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, (upcrossingsBefore a b
    (fun k ↦ X ((TimePartition.expandingDyadic n).pointNat k))
      ((TimePartition.expandingDyadic n).size + 1) ω : ℝ≥0∞)

theorem monotone_upcrossings_expandingDyadic {Ω : Type*} {a b : ℝ}
    {X : ℝ≥0 → Ω → ℝ} (hab : a < b) (ω : Ω) :
    Monotone (fun n : ℕ ↦ upcrossingsBefore a b
      (fun k ↦ X ((TimePartition.expandingDyadic n).pointNat k))
        ((TimePartition.expandingDyadic n).size + 1) ω) :=
  fun _ _ hij ↦ TimePartition.upcrossingsBefore_le_of_range_subset hab
    (TimePartition.expandingDyadic_range_mono hij)

theorem exists_max_upcrossings_expandingDyadic {Ω : Type*} {a b : ℝ}
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hf : denseUpcrossings a b X ω < ⊤) :
    ∃ n : ℕ, ∀ m : ℕ,
      upcrossingsBefore a b (fun k ↦ X ((TimePartition.expandingDyadic m).pointNat k))
        ((TimePartition.expandingDyadic m).size + 1) ω ≤
      upcrossingsBefore a b (fun k ↦ X ((TimePartition.expandingDyadic n).pointNat k))
        ((TimePartition.expandingDyadic n).size + 1) ω := by
  let c (n : ℕ) := upcrossingsBefore a b
    (fun k ↦ X ((TimePartition.expandingDyadic n).pointNat k))
      ((TimePartition.expandingDyadic n).size + 1) ω
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hf.ne
  have hb : BddAbove (Set.range c) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply (Nat.cast_le (α := ℝ≥0∞)).mp
    exact (le_iSup (fun n ↦ (c n : ℝ≥0∞)) n).trans hK.le
  obtain ⟨n, hn⟩ := Nat.sSup_mem (Set.range_nonempty c) hb
  refine ⟨n, fun m ↦ ?_⟩
  change c m ≤ c n
  rw [hn]
  exact le_csSup hb (Set.mem_range_self m)

end StochLean
