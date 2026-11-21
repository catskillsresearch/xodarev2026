/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.LeftRightLim

/-! # One-sided limits of a closed step cutoff

The right limit includes a jump at the endpoint; the strict-left limit
excludes it. The zero-time left filter may be trivial and is not asserted
to have a unique limit.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean

theorem tendsto_stepCutoff_right {E : Type*} [TopologicalSpace E] [Zero E]
    (a t : ℝ≥0) (b : E) :
    Tendsto (fun u : ℝ≥0 ↦ if a ≤ u then b else 0) (𝓝[≥] t)
      (𝓝 (if a ≤ t then b else 0)) := by
  by_cases h : a ≤ t
  · rw [if_pos h]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [if_pos (h.trans (show t ≤ u from hu))]
  · rw [if_neg h]
    have hu : ∀ᶠ u in 𝓝[≥] t, u < a :=
      (eventually_lt_nhds (lt_of_not_ge h)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [hu] with u hu
    simp only [if_neg (not_le_of_gt hu)]

theorem tendsto_stepCutoff_left {E : Type*} [TopologicalSpace E] [Zero E]
    (a t : ℝ≥0) (b : E) :
    Tendsto (fun u : ℝ≥0 ↦ if a ≤ u then b else 0) (𝓝[<] t)
      (𝓝 (if a < t then b else 0)) := by
  by_cases h : a < t
  · rw [if_pos h]
    have hu : ∀ᶠ u in 𝓝[<] t, a < u :=
      (eventually_gt_nhds h).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [hu] with u hu
    simp only [if_pos hu.le]
  · rw [if_neg h]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [if_neg (not_le_of_gt ((show u < t from hu).trans_le (le_of_not_gt h)))]

end StochLean
