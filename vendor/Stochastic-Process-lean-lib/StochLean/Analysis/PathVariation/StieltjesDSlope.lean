/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.EndpointPairStep
public import StochLean.Analysis.PathVariation.CadlagCompositionBounds
public import StochLean.Analysis.PathVariation.UniformPartition
public import StochLean.ForMathlib.Analysis.DSlopeContinuous

/-! # Exact differentiated-slope Stieltjes integration along cadlag BV paths

The finite endpoint sums telescope. Dominated convergence identifies their
limit with the actual Stieltjes integral, including at jumps.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hv : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem tendsto_stieltjesIncrementEndpointPairSum_of_cadlag
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2))
    {f : ℝ≥0 → ℝ} (hf : IsCadlagPath f) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size,
      Φ (f ((π n).left i)) (f ((π n).right i)) * (π n).increment x i) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hv hr
        (fun t ↦ Φ (Function.leftLim f t) (f t)) 0 T)) := by
  obtain ⟨C, hC, _⟩ := exists_compact_pair_bound_of_cadlag hf T hΦ
  have h := tendsto_pathStieltjesIncrementIntegral_of_dominated_convergence
    (x := x) (hx := hv) (hr := hr) (s := 0) (t := T)
    (f := fun n ↦ (π n).endpointPairStep Φ f)
    (g := fun t ↦ Φ (Function.leftLim f t) (f t)) (bound := fun _ ↦ C)
    (fun n ↦ ((π n).measurable_endpointPairStep Φ f).aestronglyMeasurable)
    (integrableOn_const measure_Ioc_lt_top.ne) (fun n ↦ ?_) ?_
  · simpa only [pathStieltjesIncrementIntegral_endpointPairStep_terminal] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (π n).norm_endpointPairStep_le Φ f hC ⟨hu.1.le, hu.2⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact TimePartition.tendsto_endpointPairStep_of_cadlag hΦ hf hu hmesh

theorem TimePartition.sum_dslope_increment (π : TimePartition T) (f : ℝ → ℝ)
    (x : ℝ≥0 → ℝ) :
    (∑ i : Fin π.size, dslope f (x (π.left i)) (x (π.right i)) * π.increment x i) =
      f (x T) - f (x 0) := by
  calc
    _ = ∑ i : Fin π.size, π.increment (f ∘ x) i := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [TimePartition.increment, Function.comp_def, smul_eq_mul, mul_comm] using
        sub_smul_dslope f (x (π.left i)) (x (π.right i))
    _ = _ := π.sum_increment (f ∘ x)

theorem pathStieltjesIncrementIntegral_dslope {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (T : ℝ≥0) :
    pathStieltjesIncrementIntegral x hv hx.1
      (fun t ↦ dslope f (Function.leftLim x t) (x t)) 0 T = f (x T) - f (x 0) := by
  let π : ℕ → TimePartition T := fun n ↦ (LocallyFinitePartition.dyadic n).restrict T
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ T))
  have h := tendsto_stieltjesIncrementEndpointPairSum_of_cadlag (hv := hv) (hr := hx.1)
    (continuous_dslope_of_contDiff hf) hx hm
  simp only [TimePartition.sum_dslope_increment] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end StochLean
