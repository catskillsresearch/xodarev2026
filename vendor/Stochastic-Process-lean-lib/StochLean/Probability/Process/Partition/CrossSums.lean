/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.SquareSums

/-! # Raw mixed increment sums and their pointwise algebra

The original pure deterministic covariation sum is used, with the separate
initial product. No adaptedness, regularity or integrability is needed here.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def quadraticCovariationSumProcess (π : StoppingTimePartition F) (X Y : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ X 0 ω * Y 0 ω +
      StochLean.covariationSum (π.path ω) (fun u ↦ X (min u t) ω) (fun u ↦ Y (min u t) ω)

theorem quadraticCovariationSumProcess_polarization (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess X Y = fun t ω ↦ (1 / 2 : ℝ) *
      (π.quadraticVariationSumProcess (X + Y) t ω - π.quadraticVariationSumProcess X t ω -
        π.quadraticVariationSumProcess Y t ω) := by
  funext t ω
  have h := StochLean.quadraticVariationSum_add (π.path ω)
    (fun u ↦ X (min u t) ω) (fun u ↦ Y (min u t) ω)
  change StochLean.quadraticVariationSum (π.path ω) (fun u ↦ (X + Y) (min u t) ω) = _ at h
  simp only [Pi.add_apply] at h
  simp only [quadraticCovariationSumProcess, quadraticVariationSumProcess, h, Pi.add_apply]
  ring

@[simp] theorem quadraticCovariationSumProcess_self (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess X X = π.quadraticVariationSumProcess X := by
  funext t ω
  simp only [quadraticCovariationSumProcess, quadraticVariationSumProcess,
    StochLean.covariationSum_self, pow_two]

theorem quadraticCovariationSumProcess_comm (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess X Y = π.quadraticCovariationSumProcess Y X := by
  funext t ω
  simp only [quadraticCovariationSumProcess, StochLean.covariationSum_comm, mul_comm]

theorem quadraticCovariationSumProcess_add_left (π : StoppingTimePartition F)
    (X Y Z : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess (X + Y) Z =
      π.quadraticCovariationSumProcess X Z + π.quadraticCovariationSumProcess Y Z := by
  funext t ω
  have h := StochLean.covariationSum_add_left (π.path ω)
    (fun u ↦ X (min u t) ω) (fun u ↦ Y (min u t) ω) (fun u ↦ Z (min u t) ω)
  change StochLean.covariationSum (π.path ω) (fun u ↦ (X + Y) (min u t) ω)
    (fun u ↦ Z (min u t) ω) = _ at h
  simp only [Pi.add_apply] at h
  simp only [quadraticCovariationSumProcess, h, Pi.add_apply]
  ring

theorem quadraticCovariationSumProcess_const_mul_left (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) (c : ℝ) :
    π.quadraticCovariationSumProcess (fun t ω ↦ c * X t ω) Y =
      c • π.quadraticCovariationSumProcess X Y := by
  funext t ω
  simp only [quadraticCovariationSumProcess, StochLean.covariationSum_mul_left,
    Pi.smul_apply, smul_eq_mul]
  ring

end ProbabilityTheory.StoppingTimePartition
