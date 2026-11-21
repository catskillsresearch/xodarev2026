/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ExpandingDyadic

/-! # The countable dense set of existing expanding-grid endpoints

This set collects the canonical partitions already used for dense upcrossings;
it does not introduce another dyadic grid or endpoint convention.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace StochLean

def dyadicSkeleton : Set ℝ≥0 := ⋃ n : ℕ, Set.range (TimePartition.expandingDyadic n).point

theorem mem_dyadicSkeleton_iff {t : ℝ≥0} : t ∈ dyadicSkeleton ↔
    ∃ n : ℕ, t ∈ Set.range (TimePartition.expandingDyadic n).point := mem_iUnion

theorem dyadicSkeleton_countable : dyadicSkeleton.Countable :=
  Set.countable_iUnion fun _ ↦ Set.countable_range _

theorem zero_mem_dyadicSkeleton : (0 : ℝ≥0) ∈ dyadicSkeleton := by
  apply mem_dyadicSkeleton_iff.mpr
  exact ⟨0, 0, (TimePartition.expandingDyadic 0).first_eq_zero⟩

theorem dyadicSkeleton_dense : Dense dyadicSkeleton := by
  intro t
  apply mem_closure_of_tendsto (TimePartition.expandingDyadic_ceilingPoint_tendsto t)
  exact Eventually.of_forall fun n ↦ mem_dyadicSkeleton_iff.mpr
    ⟨n, (TimePartition.expandingDyadic n).ceilingIndex t, rfl⟩

end StochLean
