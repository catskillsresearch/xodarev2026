/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesEndpointSums

/-! # Square sums of a cadlag finite-variation path

The limit is the Stieltjes increment integral of the actual jump. The next
identification with a jump series is separate; no summability is assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem pathStieltjesIncrementIntegral_sub {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}
    (hf : IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc s t) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIncrementIntegral x hx hr (fun u ↦ f u - g u) s t =
      pathStieltjesIncrementIntegral x hx hr f s t -
        pathStieltjesIncrementIntegral x hx hr g s t := by
  simp only [pathStieltjesIncrementIntegral,
    integral_sub (integrableOn_positiveVariationStieltjes hf)
      (integrableOn_positiveVariationStieltjes hg),
    integral_sub (integrableOn_negativeVariationStieltjes hf)
      (integrableOn_negativeVariationStieltjes hg)]
  ring

theorem pathStieltjesIncrementIntegral_endpoint_difference (π : TimePartition T) :
    pathStieltjesIncrementIntegral x hx hr
      (fun u ↦ π.taggedStep π.right x u - π.leftStep x u) 0 T =
      quadraticVariationSum π x := by
  rw [pathStieltjesIncrementIntegral_sub
    (integrableOn_variationStieltjes_taggedStep π π.right x T)
    (integrableOn_variationStieltjes_leftStep π x T),
    pathStieltjesIncrementIntegral_taggedStep_terminal,
    pathStieltjesIncrementIntegral_leftStep_terminal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [TimePartition.increment]
  ring

theorem tendsto_quadraticVariationSum_of_cadlag_finiteVariation
    (hv : LocallyBoundedVariationOn x univ) (hc : IsCadlagPath x)
    {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ quadraticVariationSum (π n) x) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hv hc.1 (fun u ↦ x u - Function.leftLim x u) 0 T)) := by
  obtain ⟨C, _, hC⟩ := hc.exists_norm_bound_Icc T
  have h := tendsto_pathStieltjesIncrementIntegral_of_dominated_convergence
    (x := x) (hx := hv) (hr := hc.1) (s := 0) (t := T)
    (f := fun n u ↦ (π n).taggedStep (π n).right x u - (π n).leftStep x u)
    (g := fun u ↦ x u - Function.leftLim x u) (bound := fun _ ↦ C + C)
    (fun n ↦ (((π n).measurable_taggedStep (π n).right x).sub
      ((π n).measurable_taggedStep (π n).left x)).aestronglyMeasurable)
    (integrableOn_const measure_Ioc_lt_top.ne) (fun n ↦ ?_) ?_
  · have he (n : ℕ) : pathStieltjesIncrementIntegral x hv hc.1
        (fun u ↦ (π n).taggedStep (π n).right x u - (π n).leftStep x u) 0 T =
        quadraticVariationSum (π n) x :=
      pathStieltjesIncrementIntegral_endpoint_difference (hx := hv) (hr := hc.1) (π n)
    simpa only [he] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (norm_sub_le _ _).trans (add_le_add
      ((π n).norm_taggedStep_le (π n).right
        (fun i ↦ ⟨bot_le, (π n).point_le_horizon _⟩) hC ⟨hu.1.le, hu.2⟩)
      ((π n).norm_taggedStep_le (π n).left
        (fun i ↦ ⟨bot_le, (π n).point_le_horizon _⟩) hC ⟨hu.1.le, hu.2⟩))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (TimePartition.tendsto_rightStep_of_continuousWithinAt hu (hc.1 u) hmesh).sub
      (TimePartition.tendsto_leftStep_of_tendsto_left hu
        (tendsto_leftLim_of_tendsto (hc.2 u (ne_of_gt hu.1))) hmesh)

theorem quadraticVariationSum_eq_square_sub_leftSum (π : TimePartition T) (x : ℝ≥0 → ℝ) :
    quadraticVariationSum π x = x T ^ 2 - x 0 ^ 2 -
      2 * ∑ i : Fin π.size, x (π.left i) * π.increment x i := by
  rw [← π.sum_increment (fun u ↦ x u ^ 2), Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [TimePartition.increment]
  ring

end StochLean
