/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.CrossSumsLinear
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess

/-! # Mixed sums of a source elementary integral

This is a finite-sum identity, before taking limits. It retains the initial
product and each random coefficient, with no moment or path hypothesis.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem integralProcess_eq_sum_stopped (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) :
    H.integralProcess X = (fun _ ω ↦ H.initial ω * X 0 ω) +
      ∑ i : Fin H.partition.size, (fun t ω ↦ H.coefficient i ω *
        (stoppedProcess X (H.partition.point i.succ).withTop t ω -
          stoppedProcess X (H.partition.point i.castSucc).withTop t ω)) := by
  funext t ω
  simp only [integralProcess_apply, Pi.add_apply, Finset.sum_apply,
    FiniteStoppingTime.stoppedProcess_eq, min_comm]

theorem quadraticCovariationSumProcess_integralProcess (H : SimplePredictableRep F)
    (π : StoppingTimePartition F) (X Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess (H.integralProcess X) Y =
      fun t ω ↦ H.initial ω * X 0 ω * Y 0 ω +
        ∑ i : Fin H.partition.size, H.coefficient i ω *
          (π.quadraticCovariationSumProcess
            (stoppedProcess X (H.partition.point i.succ).withTop) Y t ω -
          π.quadraticCovariationSumProcess
            (stoppedProcess X (H.partition.point i.castSucc).withTop) Y t ω) := by
  rw [H.integralProcess_eq_sum_stopped, π.quadraticCovariationSumProcess_add_left,
    π.quadraticCovariationSumProcess_constant_left,
    π.quadraticCovariationSumProcess_finset_sum_left]
  funext t ω
  simp only [Pi.add_apply, Finset.sum_apply,
    StoppingTimePartition.quadraticCovariationSumProcess_random_mul_left]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change H.coefficient i ω * π.quadraticCovariationSumProcess
    (stoppedProcess X (H.partition.point i.succ).withTop -
      stoppedProcess X (H.partition.point i.castSucc).withTop) Y t ω = _
  rw [π.quadraticCovariationSumProcess_sub_left]
  rfl

end ProbabilityTheory.SimplePredictableRep
