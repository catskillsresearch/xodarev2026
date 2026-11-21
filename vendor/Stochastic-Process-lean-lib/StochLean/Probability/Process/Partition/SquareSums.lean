/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.LeftSampling

/-! # Raw square-increment sums on stopping-time partitions

The pure deterministic square-sum owner is reused pathwise. The source initial
square is added exactly once. The telescoping identity is valid for arbitrary
real paths and repeated endpoints; no regularity hypothesis is required.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def quadraticVariationSumProcess (π : StoppingTimePartition F) (X : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ (X 0 ω) ^ 2 +
      StochLean.quadraticVariationSum (π.path ω) (fun u ↦ X (min u t) ω)

@[simp] theorem quadraticVariationSumProcess_zero (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) : π.quadraticVariationSumProcess X 0 = fun ω ↦ (X 0 ω) ^ 2 := by
  funext ω
  simp [quadraticVariationSumProcess]

theorem initial_sq_le_quadraticVariationSumProcess (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (X 0 ω) ^ 2 ≤ π.quadraticVariationSumProcess X t ω :=
  le_add_of_nonneg_right (StochLean.quadraticVariationSum_nonneg _ _)

theorem quadraticVariationSumProcess_eq_square_sub_riemann (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.quadraticVariationSumProcess X t ω =
      (X (min (π.terminal ω) t) ω) ^ 2 - 2 * π.leftRiemannSumProcess X X t ω := by
  let ρ := π.path ω
  have htel := ρ.sum_increment (fun u ↦ (X (min u t) ω) ^ 2)
  simp only [StochLean.TimePartition.increment, zero_min] at htel
  have hcell (i : Fin π.size) :
      (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2 =
      (X (min (π.point i.succ ω) t) ω) ^ 2 -
        (X (min (π.point i.castSucc ω) t) ω) ^ 2 -
      2 * (X (π.point i.castSucc ω) ω *
        (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω)) := by
    by_cases hi : π.point i.castSucc ω ≤ t
    · rw [min_eq_left hi]
      ring
    · have ht : t ≤ π.point i.castSucc ω := (lt_of_not_ge hi).le
      have htr : t ≤ π.point i.succ ω := ht.trans (ρ.left_le_right i)
      simp only [min_eq_right ht, min_eq_right htr, sub_self, zero_pow (by norm_num : 2 ≠ 0),
        mul_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ ↦ hcell i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  change (∑ i : Fin π.size,
    ((X (min (π.point i.succ ω) t) ω) ^ 2 -
      (X (min (π.point i.castSucc ω) t) ω) ^ 2)) = _ at htel
  rw [htel] at hs
  change (X 0 ω) ^ 2 + (∑ i : Fin π.size,
    (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2) = _
  rw [hs]
  change _ = _ - 2 * (∑ i : Fin π.size, _)
  ring

end ProbabilityTheory.StoppingTimePartition
