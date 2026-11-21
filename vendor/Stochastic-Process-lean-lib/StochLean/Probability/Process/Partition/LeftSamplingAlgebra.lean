/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.LeftSampling

/-! # Algebra of increment-only left Riemann sums

These pointwise identities impose no regularity or measurability assumptions.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem leftRiemannSumProcess_sub_integrand (π : StoppingTimePartition F)
    (Y Z X : ℝ≥0 → Ω → ℝ) :
    π.leftRiemannSumProcess (Y - Z) X =
      π.leftRiemannSumProcess Y X - π.leftRiemannSumProcess Z X := by
  funext t ω
  simp only [leftRiemannSumProcess, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

end ProbabilityTheory.StoppingTimePartition
