/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegralTagged
public import StochLean.Probability.Process.FiniteVariation.Integral

/-! # Protter I.53: tagged random-partition Stieltjes approximation

Partitions and tags can vary with the sample. All partition, mesh and integrand
conditions hold on one common event. No stopping-time condition on a tag is
needed for this pathwise result; no future-tag step process is claimed adapted.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {T : ℝ≥0}
  (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))
  {H : ℝ≥0 → Ω → ℝ} {π : ℕ → Ω → TimePartition T}

theorem ae_tendstoUniformlyOn_stieltjesTaggedSum
    (ξ : ∀ n ω, Fin (π n ω).size → ℝ≥0)
    (hξ : ∀ᵐ ω ∂P, ∀ n i, (π n ω).left i ≤ ξ n ω i ∧ ξ n ω i ≤ (π n ω).right i)
    (hH : HasContinuousPaths H P)
    (hmesh : ∀ᵐ ω ∂P, Tendsto (fun n ↦ ((π n ω).mesh : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun n ↦ stieltjesTaggedSum (π n ω) (ξ n ω) (fun t ↦ X t ω) (fun t ↦ H t ω))
      (fun t ↦ finiteVariationIntegral X hv hr H t ω) atTop (Icc 0 T) := by
  filter_upwards [hξ, hH, hmesh] with ω hξω hHω hmω
  exact tendstoUniformlyOn_stieltjesTaggedSum (fun n ↦ ξ n ω) hξω hHω.continuousOn hmω

theorem ae_tendsto_stieltjesTaggedIncrementSum
    (ξ : ∀ n ω, Fin (π n ω).size → ℝ≥0)
    (hξ : ∀ᵐ ω ∂P, ∀ n i, (π n ω).left i ≤ ξ n ω i ∧ ξ n ω i ≤ (π n ω).right i)
    (hH : HasContinuousPaths H P)
    (hmesh : ∀ᵐ ω ∂P, Tendsto (fun n ↦ ((π n ω).mesh : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ ∑ i : Fin (π n ω).size, H (ξ n ω i) ω * (π n ω).increment (fun t ↦ X t ω) i)
      atTop (𝓝 (pathStieltjesIncrementIntegral (fun t ↦ X t ω) (hv ω) (hr ω)
        (fun t ↦ H t ω) 0 T)) := by
  filter_upwards [hξ, hH, hmesh] with ω hξω hHω hmω
  exact tendsto_stieltjesTaggedIncrementSum (fun n ↦ ξ n ω) hξω hHω.continuousOn hmω

end ProbabilityTheory
