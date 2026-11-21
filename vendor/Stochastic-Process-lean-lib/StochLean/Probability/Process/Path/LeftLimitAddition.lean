/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # Addition of source left limits and jumps, including time zero -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.leftLimitProcess_add (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    leftLimitProcess (X + Y) t ω = leftLimitProcess X t ω + leftLimitProcess Y t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLimitProcess_zero, Pi.zero_apply, add_zero]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [leftLimitProcess, if_neg ht]
    exact leftLim_eq_of_tendsto
      ((hX.tendsto_leftLimitProcess ht).add (hY.tendsto_leftLimitProcess ht))

theorem IsCadlagPath.jumpProcess_add (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    jumpProcess (X + Y) t ω = jumpProcess X t ω + jumpProcess Y t ω := by
  simp only [jumpProcess, Pi.sub_apply, Pi.add_apply, hX.leftLimitProcess_add hY t]
  ring

end ProbabilityTheory
