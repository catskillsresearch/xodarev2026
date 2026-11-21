/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TotalVariation

/-! # Deterministic stopping of finite partitions

Clipping every endpoint retains repeated endpoints. This avoids arbitrary deduplication in
the pathwise stopping identity and preserves refinement and the vanishing-mesh condition.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean

namespace TimePartition

variable {T s : ℝ≥0}

/-- Stop a partition at an earlier horizon, keeping its original number of cells. -/
def stop (π : TimePartition T) (s : ℝ≥0) (hs : s ≤ T) : TimePartition s where
  size := π.size
  point i := min (π.point i) s
  monotone_point := fun _ _ hij ↦ min_le_min_right s (π.monotone_point hij)
  first_eq_zero := by simp [π.first_eq_zero]
  last_eq_horizon := by simp [π.last_eq_horizon, min_eq_right hs]

theorem increment_stop (π : TimePartition T) (hs : s ≤ T) (f : ℝ≥0 → ℝ)
    (i : Fin π.size) :
    (π.stop s hs).increment f i = π.increment (fun t ↦ f (min t s)) i := rfl

theorem gap_stop_le (π : TimePartition T) (hs : s ≤ T) (i : Fin π.size) :
    (π.stop s hs).gap i ≤ π.gap i := by
  change min (π.right i) s - min (π.left i) s ≤ π.right i - π.left i
  by_cases hl : π.left i ≤ s
  · rw [min_eq_left hl]
    exact tsub_le_tsub_right (min_le_left _ _) _
  · have hr : s ≤ π.right i := (le_of_not_ge hl).trans (π.left_le_right i)
    rw [min_eq_right hr, min_eq_right (le_of_not_ge hl), tsub_self]
    exact bot_le

theorem mesh_stop_le (π : TimePartition T) (hs : s ≤ T) :
    (π.stop s hs).mesh ≤ π.mesh :=
  Finset.sup_le (fun i _ ↦ (π.gap_stop_le hs i).trans (π.gap_le_mesh i))

theorem Refines.stop {π ρ : TimePartition T} (h : π.Refines ρ) (hs : s ≤ T) :
    (π.stop s hs).Refines (ρ.stop s hs) := by
  rintro t ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := h ⟨i, rfl⟩
  exact ⟨j, congrArg (min · s) hj⟩

theorem tendsto_mesh_stop {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) (hs : s ≤ T) :
    Tendsto (fun n ↦ (((π n).stop s hs).mesh : ℝ)) atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ NNReal.coe_nonneg _)
    (fun n ↦ by exact_mod_cast (π n).mesh_stop_le hs) hmesh

end TimePartition

theorem quadraticVariationSum_stop {T s : ℝ≥0} (π : TimePartition T) (hs : s ≤ T)
    (f : ℝ≥0 → ℝ) :
    quadraticVariationSum (π.stop s hs) f =
      quadraticVariationSum π (fun t ↦ f (min t s)) := rfl

theorem covariationSum_stop {T s : ℝ≥0} (π : TimePartition T) (hs : s ≤ T)
    (f g : ℝ≥0 → ℝ) :
    covariationSum (π.stop s hs) f g =
      covariationSum π (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) := rfl

end StochLean
