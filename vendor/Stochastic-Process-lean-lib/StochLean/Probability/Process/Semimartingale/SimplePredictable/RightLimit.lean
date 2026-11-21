/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Regularity
public import StochLean.Probability.Process.Path.StepRightLimit

/-! # Explicit right limits of the full source simple class

The independent initial spike disappears under the right-limit operation.
Every interval coefficient, including those on repeated endpoints, remains
in the exact finite formula with the right-continuous endpoint convention.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem rightLimitProcess_toProcess (H : SimplePredictableRep F) (t : ℝ≥0) (ω : Ω) :
    rightLimitProcess H.toProcess t ω = ∑ i : Fin H.partition.size,
      if H.partition.point i.castSucc ω ≤ t ∧ t < H.partition.point i.succ ω
      then H.coefficient i ω else 0 := by
  have hu := tendsto_finsetSum Finset.univ fun i _ ↦
    tendsto_step_Ioc_nhdsGT (H.partition.point i.castSucc ω)
      (H.partition.point i.succ ω) t (H.coefficient i ω)
  apply rightLim_eq_of_tendsto
  apply hu.congr'
  filter_upwards [self_mem_nhdsWithin] with u htu
  have hu0 : u ≠ 0 := ne_of_gt ((show (0 : ℝ≥0) ≤ t from bot_le).trans_lt htu)
  simp only [toProcess, if_neg hu0]

end ProbabilityTheory.SimplePredictableRep
