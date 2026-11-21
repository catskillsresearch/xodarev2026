/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.CrossSums

/-! # Finite random-coefficient algebra of raw mixed sums

These are exact identities for arbitrary paths. Coefficients are fixed in
time but may be arbitrary functions of the sample point; no adaptedness or
semimartingale claim for a multiplied path is made here.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem quadraticCovariationSumProcess_constant_left (π : StoppingTimePartition F)
    (c : Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess (fun _ ↦ c) Y = fun _ ω ↦ c ω * Y 0 ω := by
  funext t ω
  simp [quadraticCovariationSumProcess, StochLean.covariationSum, StochLean.TimePartition.increment]

theorem quadraticCovariationSumProcess_random_mul_left (π : StoppingTimePartition F)
    (c : Ω → ℝ) (X Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess (fun t ω ↦ c ω * X t ω) Y =
      fun t ω ↦ c ω * π.quadraticCovariationSumProcess X Y t ω := by
  funext t ω
  simp only [quadraticCovariationSumProcess, StochLean.covariationSum,
    StochLean.TimePartition.increment, ← mul_sub, mul_assoc, ← Finset.mul_sum, mul_add]

theorem quadraticCovariationSumProcess_sub_left (π : StoppingTimePartition F)
    (X Z Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess (X - Z) Y =
      π.quadraticCovariationSumProcess X Y - π.quadraticCovariationSumProcess Z Y := by
  have heq : X - Z = X + (fun t ω ↦ (-1 : ℝ) * Z t ω) := by
    funext t ω
    simp only [Pi.sub_apply, Pi.add_apply, neg_one_mul, sub_eq_add_neg]
  rw [heq, quadraticCovariationSumProcess_add_left,
    quadraticCovariationSumProcess_const_mul_left]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem quadraticCovariationSumProcess_finset_sum_left (π : StoppingTimePartition F)
    {ι : Type*} (s : Finset ι) (Z : ι → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess (∑ i ∈ s, Z i) Y =
      ∑ i ∈ s, π.quadraticCovariationSumProcess (Z i) Y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (π.quadraticCovariationSumProcess_constant_left 0 Y).trans (by funext t ω; simp)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, quadraticCovariationSumProcess_add_left, ih]

end ProbabilityTheory.StoppingTimePartition
