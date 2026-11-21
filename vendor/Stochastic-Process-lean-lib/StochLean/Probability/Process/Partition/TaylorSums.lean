/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TaylorSums
public import StochLean.Probability.Process.Partition.WeightedCrossSums

/-! # Exact Taylor error process on finite stopping-time partitions -/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def quadraticTaylorErrorProcess (π : StoppingTimePartition F)
    (f : ℝ → ℝ) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  StochLean.quadraticTaylorErrorSum (π.path ω) f (X · ω) t

theorem quadraticTaylorErrorProcess_eq_riemann (π : StoppingTimePartition F)
    (f : ℝ → ℝ) (X : ℝ≥0 → Ω → ℝ) :
    π.quadraticTaylorErrorProcess f X = fun t ω ↦
      f (X (min (π.terminal ω) t) ω) - f (X 0 ω) -
        π.leftRiemannSumProcess (fun u v ↦ deriv f (X u v)) X t ω -
        (1 / 2 : ℝ) * π.weightedQuadraticCovariationSumProcess
          (fun u v ↦ deriv (deriv f) (X u v)) X X t ω := by
  funext t ω
  have h := (π.path ω).taylor_sum_with_remainder f (X · ω) t
  have hs : (∑ i : Fin π.size, deriv (deriv f) (X (π.point i.castSucc ω) ω) *
      (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2) =
      π.weightedQuadraticCovariationSumProcess
        (fun u v ↦ deriv (deriv f) (X u v)) X X t ω := by
    unfold weightedQuadraticCovariationSumProcess
    apply sum_congr rfl
    intro i _
    ring
  change f (X (min (π.terminal ω) t) ω) - f (X 0 ω) =
    π.leftRiemannSumProcess (fun u v ↦ deriv f (X u v)) X t ω +
    (1 / 2 : ℝ) * (∑ i : Fin π.size, deriv (deriv f) (X (π.point i.castSucc ω) ω) *
      (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2) +
    π.quadraticTaylorErrorProcess f X t ω at h
  rw [hs] at h
  linarith only [h]

end ProbabilityTheory.StoppingTimePartition
