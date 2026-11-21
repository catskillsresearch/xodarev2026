/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TaggedStepApproximation
public import StochLean.Analysis.PathVariation.StieltjesIntegralRiemann

/-! # Arbitrarily tagged Stieltjes Riemann sums

The tags lie in their closed cells. Neither nested partitions nor continuity
of the locally BV integrator is required. Partial terminal cells are retained.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0}

noncomputable def stieltjesTaggedSum (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (x f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f 0 * x 0 + ∑ i : Fin π.size, f (ξ i) *
    (x (min (π.right i) t) - x (min (π.left i) t))

theorem stieltjesTaggedSum_terminal (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (x f : ℝ≥0 → ℝ) :
    stieltjesTaggedSum π ξ x f T = f 0 * x 0 + ∑ i : Fin π.size, f (ξ i) * π.increment x i := by
  simp only [stieltjesTaggedSum, TimePartition.increment, TimePartition.left, TimePartition.right,
    min_eq_left (π.point_le_horizon _)]

theorem stieltjesTaggedSum_left (π : TimePartition T) (x f : ℝ≥0 → ℝ) :
    stieltjesTaggedSum π π.left x f = stieltjesLeftSum π x f := rfl

variable {x : ℝ≥0 → ℝ} {hv : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem integrableOn_variationStieltjes_taggedStep (π : TimePartition T)
    (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    IntegrableOn (π.taggedStep ξ f) (Ioc 0 t) (totalVariationStieltjes x hv hr).measure :=
  integrableOn_variationStieltjes_finite_step π.left π.right (fun i ↦ f (ξ i)) (f 0) t

theorem pathStieltjesIntegral_taggedStep (π : TimePartition T)
    (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) :
    pathStieltjesIntegral x hv hr (π.taggedStep ξ f) = stieltjesTaggedSum π ξ x f := by
  funext t
  exact pathStieltjesIntegral_finite_step π.left π.right (fun i ↦ f (ξ i)) π.left_le_right (f 0) t

theorem tendstoUniformlyOn_stieltjesTaggedSum {π : ℕ → TimePartition T}
    (ξ : ∀ n, Fin (π n).size → ℝ≥0)
    (hξ : ∀ n i, (π n).left i ≤ ξ n i ∧ ξ n i ≤ (π n).right i)
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n ↦ stieltjesTaggedSum (π n) (ξ n) x f)
      (pathStieltjesIntegral x hv hr f) atTop (Icc 0 T) := by
  have h := tendstoUniformlyOn_pathStieltjesIntegral
    (fun n ↦ integrableOn_variationStieltjes_taggedStep
      (x := x) (hv := hv) (hr := hr) (π n) (ξ n) f T)
    (integrableOn_variationStieltjes_of_continuousOn hf)
    (TimePartition.tendstoUniformlyOn_taggedStep ξ hξ hf hmesh)
  simpa only [pathStieltjesIntegral_taggedStep] using h

theorem tendsto_stieltjesTaggedSum_terminal {π : ℕ → TimePartition T}
    (ξ : ∀ n, Fin (π n).size → ℝ≥0)
    (hξ : ∀ n i, (π n).left i ≤ ξ n i ∧ ξ n i ≤ (π n).right i)
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ f 0 * x 0 + ∑ i : Fin (π n).size, f (ξ n i) * (π n).increment x i)
      atTop (𝓝 (pathStieltjesIntegral x hv hr f T)) := by
  have h := (tendstoUniformlyOn_stieltjesTaggedSum (x := x) (hv := hv) (hr := hr)
    ξ hξ hf hmesh).tendsto_at (show T ∈ Icc 0 T from ⟨bot_le, le_rfl⟩)
  simpa only [stieltjesTaggedSum_terminal] using h

theorem tendsto_stieltjesTaggedIncrementSum {π : ℕ → TimePartition T}
    (ξ : ∀ n, Fin (π n).size → ℝ≥0)
    (hξ : ∀ n i, (π n).left i ≤ ξ n i ∧ ξ n i ≤ (π n).right i)
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size, f (ξ n i) * (π n).increment x i)
      atTop (𝓝 (pathStieltjesIncrementIntegral x hv hr f 0 T)) := by
  have h := tendsto_stieltjesTaggedSum_terminal (x := x) (hv := hv) (hr := hr) ξ hξ hf hmesh
  simpa only [pathStieltjesIntegral, add_sub_cancel_left] using h.sub_const (f 0 * x 0)

end StochLean
