/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightLimit

/-! # Cadlag reconstruction from the right limits of source left limits

Although the source left limit is set to zero initially, its right limit at
zero recovers the original initial value of a right-continuous path.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

theorem IsCadlagPath.rightLimitProcess_leftLimitProcess {ω : Ω}
    (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    rightLimitProcess (leftLimitProcess X) t ω = X t ω := by
  apply rightLim_eq_of_tendsto
  apply (hX.1 t).tendsto_leftLim_nhdsGT.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt ((show (0 : ℝ≥0) ≤ t from bot_le).trans_lt hs)
  simp only [leftLimitProcess, if_neg hs0]

theorem HasCadlagPaths.rightLimitProcess_leftLimitProcess
    (hX : HasCadlagPaths X P) :
    Indistinguishable (rightLimitProcess (leftLimitProcess X)) X P :=
  hX.mono fun _ hω ↦ hω.rightLimitProcess_leftLimitProcess

end ProbabilityTheory
