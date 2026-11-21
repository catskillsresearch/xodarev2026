/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit

/-! # Left limits of finite stopped paths

At the stopping endpoint the strict-left limit is the original strict-left limit,
not the stopped value after its jump.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.tendsto_min_const_nhdsLT (hX : IsCadlagPath (X · ω))
    {t : ℝ≥0} (ht : t ≠ 0) (a : ℝ≥0) :
    Tendsto (fun s ↦ X (min a s) ω) (𝓝[<] t)
      (𝓝 (if a < t then X a ω else leftLimitProcess X t ω)) := by
  by_cases ha : a < t
  · rw [if_pos ha]
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with s hs
    rw [min_eq_left hs.le]
  · rw [if_neg ha]
    apply (hX.tendsto_leftLimitProcess ht).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [min_eq_right (hs.le.trans (le_of_not_gt ha))]

end ProbabilityTheory
