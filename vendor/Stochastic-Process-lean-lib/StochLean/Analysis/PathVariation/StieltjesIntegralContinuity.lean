/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegral
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Uniform continuity of finite-horizon Stieltjes integration

The pathwise operator bound includes the initial value. Local uniform convergence
therefore passes through the integral uniformly in its terminal time.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f g : ℝ≥0 → ℝ} {T t : ℝ≥0}

theorem pathStieltjesIntegral_congr {y : ℝ≥0 → ℝ}
    {hy : LocallyBoundedVariationOn y univ} {hyr : ∀ t, ContinuousWithinAt y (Ici t) t}
    (hxy : x = y) (hfg : f = g) :
    pathStieltjesIntegral x hx hr f = pathStieltjesIntegral y hy hyr g := by
  subst y
  subst g
  rfl

theorem pathStieltjesIntegral_add
    (hf : IntegrableOn f (Ioc 0 t) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc 0 t) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIntegral x hx hr (fun u ↦ f u + g u) t =
      pathStieltjesIntegral x hx hr f t + pathStieltjesIntegral x hx hr g t := by
  simp only [pathStieltjesIntegral, pathStieltjesIncrementIntegral_add hf hg]
  ring

theorem pathStieltjesIntegral_const_mul (c : ℝ) (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathStieltjesIntegral x hx hr (fun u ↦ c * f u) t =
      c * pathStieltjesIntegral x hx hr f t := by
  simp only [pathStieltjesIntegral, pathStieltjesIncrementIntegral_const_mul]
  ring

theorem pathStieltjesIntegral_sub
    (hf : IntegrableOn f (Ioc 0 t) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc 0 t) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIntegral x hx hr (fun u ↦ f u - g u) t =
      pathStieltjesIntegral x hx hr f t - pathStieltjesIntegral x hx hr g t := by
  simp only [pathStieltjesIntegral, pathStieltjesIncrementIntegral,
    integral_sub (integrableOn_positiveVariationStieltjes hf)
      (integrableOn_positiveVariationStieltjes hg),
    integral_sub (integrableOn_negativeVariationStieltjes hf)
      (integrableOn_negativeVariationStieltjes hg)]
  ring

theorem norm_pathStieltjesIntegral_sub_le
    (hf : IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ u ∈ Icc 0 T, ‖f u - g u‖ ≤ C) (ht : t ≤ T) :
    ‖pathStieltjesIntegral x hx hr f t - pathStieltjesIntegral x hx hr g t‖ ≤
      C * (|x 0| + pathTotalVariation x T) := by
  have hsub : Ioc 0 t ⊆ Ioc 0 T := fun _ hu ↦ ⟨hu.1, hu.2.trans ht⟩
  rw [← pathStieltjesIntegral_sub (hf.mono_set hsub) (hg.mono_set hsub)]
  exact (norm_pathStieltjesIntegral_le (fun u hu ↦ hfg u ⟨hu.1, hu.2.trans ht⟩)).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (pathTotalVariation_monotone hx ht)) hC)

theorem tendstoUniformlyOn_pathStieltjesIntegral {ι : Type*} {l : Filter ι}
    {f : ι → ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ}
    (hf : ∀ i, IntegrableOn (f i) (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    (hfg : TendstoUniformlyOn f g l (Icc 0 T)) :
    TendstoUniformlyOn (fun i ↦ pathStieltjesIntegral x hx hr (f i))
      (pathStieltjesIntegral x hx hr g) l (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let C : ℝ := |x 0| + pathTotalVariation x T
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (pathTotalVariation_nonneg x T)
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hfg (ε / (C + 1)) hδ] with i hi
  intro t ht
  rw [dist_eq_norm_sub]
  have hb := norm_pathStieltjesIntegral_sub_le hg (hf i) hδ.le
    (fun u hu ↦ (show ‖g u - f i u‖ < ε / (C + 1) from hi u hu).le) ht.2
  apply hb.trans_lt
  change ε / (C + 1) * C < ε
  calc
    _ < ε / (C + 1) * (C + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ _ (by linarith)

end StochLean
