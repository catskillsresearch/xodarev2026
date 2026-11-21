/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VectorTaylorSums
public import StochLean.ForMathlib.Analysis.FiniteCoordinateDerivatives
public import StochLean.Probability.Process.Partition.WeightedCrossSums

/-! # Exact coordinate Taylor sums on finite stopping-time partitions

Every derivative term is an existing scalar left-Riemann or weighted mixed
sum. The partial terminal cell and all ordered coordinate pairs are retained.
-/

@[expose] public section

open MeasureTheory Finset StochLean
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
  {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def frechetTaylorErrorProcess (π : StoppingTimePartition F)
    (f : (ι → ℝ) → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  frechetTaylorErrorSum (π.path ω) f (fun u i ↦ X i u ω) t

theorem frechetTaylorErrorProcess_eq_riemann (π : StoppingTimePartition F)
    (f : (ι → ℝ) → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) :
    π.frechetTaylorErrorProcess f X = fun t ω ↦
      f (fun i ↦ X i (min (π.terminal ω) t) ω) - f (fun i ↦ X i 0 ω) -
        (∑ i, π.leftRiemannSumProcess (fun u v ↦ coordinateDeriv f i (fun j ↦ X j u v))
          (X i) t ω) -
        (1 / 2 : ℝ) * ∑ i, ∑ j, π.weightedQuadraticCovariationSumProcess
          (fun u v ↦ coordinateSecondDeriv f i j (fun k ↦ X k u v)) (X i) (X j) t ω := by
  funext t ω
  have h := (π.path ω).frechet_taylor_sum_with_remainder f (fun u i ↦ X i u ω) t
  have h₁ : (∑ k : Fin π.size,
      fderiv ℝ f (fun i ↦ X i (π.point k.castSucc ω) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)) =
      ∑ i, π.leftRiemannSumProcess (fun u v ↦ coordinateDeriv f i (fun j ↦ X j u v))
        (X i) t ω := by
    simp_rw [fderiv_apply_eq_sum_coordinateDeriv]
    rw [sum_comm]
    rfl
  have h₂ : (∑ k : Fin π.size,
      fderiv ℝ (fderiv ℝ f) (fun i ↦ X i (π.point k.castSucc ω) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)) =
      ∑ i, ∑ j, π.weightedQuadraticCovariationSumProcess
        (fun u v ↦ coordinateSecondDeriv f i j (fun k ↦ X k u v)) (X i) (X j) t ω := by
    simp_rw [second_fderiv_apply_eq_sum_coordinateSecondDeriv]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
    rfl
  change f (fun i ↦ X i (min (π.terminal ω) t) ω) - f (fun i ↦ X i 0 ω) =
    (∑ k : Fin π.size, fderiv ℝ f (fun i ↦ X i (π.point k.castSucc ω) ω)
      (fun i ↦ X i (min (π.point k.succ ω) t) ω -
        X i (min (π.point k.castSucc ω) t) ω)) +
    (1 / 2 : ℝ) * (∑ k : Fin π.size,
      fderiv ℝ (fderiv ℝ f) (fun i ↦ X i (π.point k.castSucc ω) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)) + π.frechetTaylorErrorProcess f X t ω at h
  rw [h₁, h₂] at h
  linarith only [h]

end ProbabilityTheory.StoppingTimePartition
