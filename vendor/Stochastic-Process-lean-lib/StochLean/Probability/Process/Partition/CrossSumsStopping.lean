/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.CrossSums

/-! # Simultaneous stopping of both arguments of a mixed increment sum

This exact finite-partition identity does not assert that stopping only one
argument commutes with the sum: that assertion fails inside a partition cell.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem quadraticCovariationSumProcess_stoppedProcess (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    π.quadraticCovariationSumProcess (stoppedProcess X τ) (stoppedProcess Y τ) =
      stoppedProcess (π.quadraticCovariationSumProcess X Y) τ := by
  funext t ω
  cases hτ : τ ω with
  | top =>
    simp only [quadraticCovariationSumProcess, MeasureTheory.stoppedProcess, hτ,
      min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
  | coe a =>
    simp only [quadraticCovariationSumProcess, MeasureTheory.stoppedProcess, hτ,
      ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, zero_min, min_assoc]

end ProbabilityTheory.StoppingTimePartition
