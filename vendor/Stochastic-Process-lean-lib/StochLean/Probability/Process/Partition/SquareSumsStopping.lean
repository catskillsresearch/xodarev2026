/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.SquareSums

/-! # Stopping commutes with the actual raw square-increment sums

The random time can be infinite and need not be a stopping time for this
pathwise algebraic identity.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem quadraticVariationSumProcess_stoppedProcess (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    π.quadraticVariationSumProcess (stoppedProcess X τ) =
      stoppedProcess (π.quadraticVariationSumProcess X) τ := by
  funext t ω
  cases hτ : τ ω with
  | top =>
    simp only [quadraticVariationSumProcess, MeasureTheory.stoppedProcess, hτ,
      min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
  | coe a =>
    simp only [quadraticVariationSumProcess, MeasureTheory.stoppedProcess, hτ,
      ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, zero_min, min_assoc]

end ProbabilityTheory.StoppingTimePartition
