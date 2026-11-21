/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LeftStepApproximation
public import Mathlib.Order.Filter.Finite

/-! # Fine partitions separate any prescribed finite collection of times -/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace StochLean.TimePartition

theorem dist_le_mesh_of_mem_cell {T : ℝ≥0} (π : TimePartition T) {i : Fin π.size}
    {s r : ℝ≥0} (hs : s ∈ Icc (π.left i) (π.right i))
    (hr : r ∈ Icc (π.left i) (π.right i)) : dist s r ≤ (π.mesh : ℝ) := by
  apply le_trans (b := (π.gap i : ℝ)) _ (by exact_mod_cast π.gap_le_mesh i)
  have hsl : (π.left i : ℝ) ≤ s := by exact_mod_cast hs.1
  have hsr : (s : ℝ) ≤ π.right i := by exact_mod_cast hs.2
  have hrl : (π.left i : ℝ) ≤ r := by exact_mod_cast hr.1
  have hrr : (r : ℝ) ≤ π.right i := by exact_mod_cast hr.2
  rw [NNReal.dist_eq, gap, NNReal.coe_sub (π.left_le_right i), abs_le]
  constructor <;> linarith only [hsl, hsr, hrl, hrr]

theorem eventually_separate_finite_times {T : ℝ≥0} {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) (A : Finset ℝ≥0) :
    ∀ᶠ n in atTop, ∀ i : Fin (π n).size, ∀ s ∈ A, ∀ r ∈ A,
      s ∈ Ioc ((π n).left i) ((π n).right i) →
        r ∈ Ioc ((π n).left i) ((π n).right i) → s = r := by
  have hdist : ∀ᶠ n in atTop, ∀ s ∈ A, ∀ r ∈ A, s ≠ r →
      ((π n).mesh : ℝ) < dist s r := by
    apply (eventually_all_finset A).mpr
    intro s _
    apply (eventually_all_finset A).mpr
    intro r _
    by_cases hsr : s = r
    · exact Eventually.of_forall (fun _ h ↦ (h hsr).elim)
    · exact (hmesh.eventually_lt_const (dist_pos.mpr hsr)).mono (fun _ h _ ↦ h)
  filter_upwards [hdist] with n hn
  intro i s hs r hr hsc hrc
  by_contra hne
  have hbound := (π n).dist_le_mesh_of_mem_cell ⟨hsc.1.le, hsc.2⟩ ⟨hrc.1.le, hrc.2⟩
  exact (not_lt_of_ge hbound) (hn s hs r hr hne)

end StochLean.TimePartition
