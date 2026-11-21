/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightLimit

/-! # Right limits of left-open, right-closed interval steps

The strict-right limit reverses the endpoint convention. The formula includes
degenerate intervals and is independent of the initial-spike convention.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem tendsto_step_Ioc_nhdsGT (a b t : ℝ≥0) (c : ℝ) :
    Tendsto (fun u : ℝ≥0 ↦ if a < u ∧ u ≤ b then c else 0) (𝓝[>] t)
      (𝓝 (if a ≤ t ∧ t < b then c else 0)) := by
  apply tendsto_const_nhds.congr'
  by_cases ha : a ≤ t
  · by_cases hb : t < b
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with u htu hub
      simp [ha, hb, ha.trans_lt htu, hub.le]
    · filter_upwards [self_mem_nhdsWithin] with u htu
      have hbu : b < u := (le_of_not_gt hb).trans_lt htu
      simp [hb, not_le_of_gt hbu]
  · filter_upwards [(eventually_lt_nhds (lt_of_not_ge ha)).filter_mono nhdsWithin_le_nhds]
      with u hua
    simp [ha, not_lt_of_ge hua.le]

end ProbabilityTheory
