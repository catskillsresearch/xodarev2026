/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.CrossSumsProduct

/-! # Actual weighted mixed increment sums

Weights are sampled at the original left endpoints. The moving partial cell
is retained, and zero-length cells are allowed. These increment sums have no
initial atom, unlike the raw mixed bracket itself.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def weightedQuadraticCovariationSumProcess (π : StoppingTimePartition F)
    (H X Y : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  ∑ i : Fin π.size, H (π.point i.castSucc ω) ω *
    (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) *
    (Y (min (π.point i.succ ω) t) ω - Y (min (π.point i.castSucc ω) t) ω)

@[simp] theorem weightedQuadraticCovariationSumProcess_zero (π : StoppingTimePartition F)
    (H X Y : ℝ≥0 → Ω → ℝ) : π.weightedQuadraticCovariationSumProcess H X Y 0 = 0 := by
  funext ω
  simp [weightedQuadraticCovariationSumProcess]

theorem weightedQuadraticCovariationSumProcess_eq_riemann (π : StoppingTimePartition F)
    (H X Y : ℝ≥0 → Ω → ℝ) :
    π.weightedQuadraticCovariationSumProcess H X Y =
      π.leftRiemannSumProcess H (X * Y) - π.leftRiemannSumProcess (H * X) Y -
        π.leftRiemannSumProcess (H * Y) X := by
  funext t ω
  simp only [weightedQuadraticCovariationSumProcess, leftRiemannSumProcess,
    Pi.sub_apply, Pi.mul_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : π.point i.castSucc ω ≤ t
  · rw [min_eq_left hi]
    ring
  · have ht : t ≤ π.point i.castSucc ω := (lt_of_not_ge hi).le
    have htr : t ≤ π.point i.succ ω := ht.trans ((π.path ω).left_le_right i)
    simp only [min_eq_right ht, min_eq_right htr, sub_self, mul_zero]

theorem weightedQuadraticCovariationSumProcess_const_left (π : StoppingTimePartition F)
    (H : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) :
    π.weightedQuadraticCovariationSumProcess H (fun _ ↦ Z) Y = 0 := by
  funext t ω
  simp [weightedQuadraticCovariationSumProcess]

theorem weightedQuadraticCovariationSumProcess_one (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) :
    π.weightedQuadraticCovariationSumProcess 1 X Y =
      fun t ω ↦ π.quadraticCovariationSumProcess X Y t ω - X 0 ω * Y 0 ω := by
  funext t ω
  simp only [weightedQuadraticCovariationSumProcess, quadraticCovariationSumProcess,
    StochLean.covariationSum, StochLean.TimePartition.increment, Pi.one_apply, one_mul]
  rw [add_sub_cancel_left]
  rfl

end ProbabilityTheory.StoppingTimePartition
