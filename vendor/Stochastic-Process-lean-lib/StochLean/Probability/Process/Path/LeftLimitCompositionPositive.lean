/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # Continuous composition of source left limits at positive times

Unlike the all-time identity, this result does not require the transformation
to preserve zero. The source left-limit process is separately zero at time zero.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.leftLimitProcess_continuous_comp_of_pos
    (hX : IsCadlagPath (X · ω)) {f : ℝ → ℝ} (hf : Continuous f)
    {t : ℝ≥0} (ht : 0 < t) :
    leftLimitProcess (fun s v ↦ f (X s v)) t ω = f (leftLimitProcess X t ω) := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  rw [leftLimitProcess, if_neg (ne_of_gt ht)]
  exact leftLim_eq_of_tendsto
    (hf.continuousAt.tendsto.comp (hX.tendsto_leftLimitProcess (ne_of_gt ht)))

end ProbabilityTheory
