/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.LeftSampling
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.RightLimit
public import StochLean.Analysis.PathVariation.LeftStepCeiling

/-! # Exact random Riemann sums of a right-limit source step process

Every source endpoint is moved to its ceiling in the sampling partition.
The formula is pathwise for arbitrary integrators and includes no initial
product because the left Riemann sum is increment-only.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem leftRiemannSum_rightLimitProcess (H : SimplePredictableRep F)
    (π : StoppingTimePartition F) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.leftRiemannSumProcess (rightLimitProcess H.toProcess) X t ω =
      ∑ j : Fin H.partition.size, H.coefficient j ω *
        (X (min ((π.path ω).ceilingPoint (H.partition.point j.succ ω)) t) ω -
          X (min ((π.path ω).ceilingPoint (H.partition.point j.castSucc ω)) t) ω) := by
  unfold StoppingTimePartition.leftRiemannSumProcess
  simp_rw [H.rightLimitProcess_toProcess, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (π.path ω).sum_increment_step_Ico ((H.partition.path ω).left_le_right j)
    (H.coefficient j ω) (fun u ↦ X (min u t) ω)

end ProbabilityTheory.SimplePredictableRep
