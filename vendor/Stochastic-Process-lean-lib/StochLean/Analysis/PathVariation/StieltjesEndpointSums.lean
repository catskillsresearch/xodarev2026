/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.EndpointStepConvergence
public import StochLean.Analysis.PathVariation.StieltjesIntegralRiemann
public import StochLean.Probability.Process.Path.CadlagBounded
public import Mathlib.Topology.Order.LeftRightLim

/-! # Stieltjes endpoint sums for cadlag integrands

Dominated convergence uses the actual total-variation measure on a finite
horizon. Left sums converge to the strict-left integrand and right sums to
the original integrand. These are increment integrals, without an initial atom.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem integrableOn_variationStieltjes_taggedStep (π : TimePartition T)
    (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    IntegrableOn (π.taggedStep ξ f) (Ioc 0 t) (totalVariationStieltjes x hx hr).measure :=
  integrableOn_variationStieltjes_finite_step π.left π.right (fun i ↦ f (ξ i)) (f 0) t

theorem pathStieltjesIncrementIntegral_taggedStep_terminal (π : TimePartition T)
    (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) :
    pathStieltjesIncrementIntegral x hx hr (π.taggedStep ξ f) 0 T =
      ∑ i : Fin π.size, f (ξ i) * π.increment x i := by
  have h := pathStieltjesIntegral_finite_step (x := x) (hx := hx) (hr := hr)
    π.left π.right (fun i ↦ f (ξ i)) π.left_le_right (f 0) T
  change pathStieltjesIntegral x hx hr (π.taggedStep ξ f) T = _ at h
  rw [pathStieltjesIntegral, TimePartition.taggedStep_zero] at h
  apply add_left_cancel (a := f 0 * x 0)
  convert h using 1
  simp only [TimePartition.increment, TimePartition.left, TimePartition.right,
    min_eq_left (π.point_le_horizon _)]

theorem pathStieltjesIncrementIntegral_leftStep_terminal (π : TimePartition T)
    (f : ℝ≥0 → ℝ) :
    pathStieltjesIncrementIntegral x hx hr (π.leftStep f) 0 T =
      ∑ i : Fin π.size, f (π.left i) * π.increment x i :=
  pathStieltjesIncrementIntegral_taggedStep_terminal π π.left f

theorem tendsto_stieltjesIncrementLeftSum_of_cadlag {π : ℕ → TimePartition T}
    {f : ℝ≥0 → ℝ} (hf : IsCadlagPath f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size, f ((π n).left i) * (π n).increment x i) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hx hr (Function.leftLim f) 0 T)) := by
  obtain ⟨C, _, hC⟩ := hf.exists_norm_bound_Icc T
  have h := tendsto_pathStieltjesIncrementIntegral_of_dominated_convergence
    (x := x) (hx := hx) (hr := hr) (s := 0) (t := T) (f := fun n ↦ (π n).leftStep f)
    (g := Function.leftLim f) (bound := fun _ ↦ C)
    (fun n ↦ ((π n).measurable_taggedStep (π n).left f).aestronglyMeasurable)
    (integrableOn_const measure_Ioc_lt_top.ne) (fun n ↦ ?_) ?_
  · simpa only [pathStieltjesIncrementIntegral_leftStep_terminal] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (π n).norm_taggedStep_le (π n).left
      (fun i ↦ ⟨bot_le, (π n).point_le_horizon _⟩) hC ⟨hu.1.le, hu.2⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact TimePartition.tendsto_leftStep_of_tendsto_left hu
      (tendsto_leftLim_of_tendsto (hf.2 u (ne_of_gt hu.1))) hmesh

theorem tendsto_stieltjesIncrementRightSum_of_cadlag {π : ℕ → TimePartition T}
    {f : ℝ≥0 → ℝ} (hf : IsCadlagPath f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size, f ((π n).right i) * (π n).increment x i) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hx hr f 0 T)) := by
  obtain ⟨C, _, hC⟩ := hf.exists_norm_bound_Icc T
  have h := tendsto_pathStieltjesIncrementIntegral_of_dominated_convergence
    (x := x) (hx := hx) (hr := hr) (s := 0) (t := T)
    (f := fun n ↦ (π n).taggedStep (π n).right f) (g := f) (bound := fun _ ↦ C)
    (fun n ↦ ((π n).measurable_taggedStep (π n).right f).aestronglyMeasurable)
    (integrableOn_const measure_Ioc_lt_top.ne) (fun n ↦ ?_) ?_
  · simpa only [pathStieltjesIncrementIntegral_taggedStep_terminal] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (π n).norm_taggedStep_le (π n).right
      (fun i ↦ ⟨bot_le, (π n).point_le_horizon _⟩) hC ⟨hu.1.le, hu.2⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact TimePartition.tendsto_rightStep_of_continuousWithinAt hu (hf.1 u) hmesh

end StochLean
