/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CompletedSums
public import StochLean.Analysis.PathVariation.LeftStepCeiling

/-! # Monotone endpoint-projected square sums

Partial-cell square sums need not increase in time. At partition endpoints
they equal completed-cell sums; composing with the monotone upper endpoint
projection therefore gives genuinely increasing approximants, even for jumps.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean

variable {T : ℝ≥0}

theorem quadraticVariationSum_stop_eq_completed_of_mem_point
    (π : TimePartition T) (f : ℝ≥0 → ℝ) {s : ℝ≥0} (hs : s ∈ Set.range π.point) :
    quadraticVariationSum π (fun t ↦ f (min t s)) = completedQuadraticVariationSum π f s := by
  classical
  unfold quadraticVariationSum completedQuadraticVariationSum cumulativeStepSum
  apply Finset.sum_congr rfl
  intro i _
  rcases π.endpoint_le_left_or_right_le hs i with h | h
  · by_cases hr : π.right i ≤ s
    · have hle : π.left i ≤ s := (π.left_le_right i).trans hr
      simp only [TimePartition.increment, if_pos hr, min_eq_left hr, min_eq_left hle]
    · have hsr : s ≤ π.right i := h.trans (π.left_le_right i)
      simp only [TimePartition.increment, if_neg hr, min_eq_right h, min_eq_right hsr,
        sub_self, zero_pow (by norm_num : 2 ≠ 0)]
  · have hl := (π.left_le_right i).trans h
    simp only [TimePartition.increment, if_pos h, min_eq_left h, min_eq_left hl]

theorem monotone_quadraticVariationSum_stop_ceilingPoint
    (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    Monotone (fun s ↦ quadraticVariationSum π (fun t ↦ f (min t (π.ceilingPoint s)))) := by
  intro s t hst
  change quadraticVariationSum π (fun u ↦ f (min u (π.ceilingPoint s))) ≤
    quadraticVariationSum π (fun u ↦ f (min u (π.ceilingPoint t)))
  rw [quadraticVariationSum_stop_eq_completed_of_mem_point π f (π.ceilingPoint_mem s),
    quadraticVariationSum_stop_eq_completed_of_mem_point π f (π.ceilingPoint_mem t)]
  exact completedQuadraticVariationSum_mono π f (π.ceilingPoint_mono hst)

end StochLean
