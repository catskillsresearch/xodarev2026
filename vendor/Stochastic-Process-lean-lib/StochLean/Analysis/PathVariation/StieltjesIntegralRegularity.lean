/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegral
public import StochLean.ForMathlib.StieltjesPrimitiveRegularity
public import StochLean.ForMathlib.VariationAlgebra
public import StochLean.Probability.Process.Path.Algebra

/-! # Cadlag finite-variation paths of Stieltjes integrals

Local pathwise integrability against total variation suffices. It is neither
an expected-variation bound nor an integrability condition on the initial value.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem monotone_integral_Ioc_of_nonneg {μ : Measure ℝ≥0} {g : ℝ≥0 → ℝ}
    (hg : ∀ T, IntegrableOn g (Ioc 0 T) μ) (h0 : ∀ u, 0 ≤ g u) :
    Monotone (fun t ↦ ∫ u in Ioc 0 t, g u ∂μ) := by
  intro s t hst
  apply setIntegral_mono_set (hg t) (Eventually.of_forall h0)
  exact Eventually.of_forall (fun u hu ↦ ⟨hu.1, hu.2.trans hst⟩)

theorem locallyBoundedVariationOn_integral_Ioc {μ : Measure ℝ≥0} {g : ℝ≥0 → ℝ}
    (hg : ∀ T, IntegrableOn g (Ioc 0 T) μ) :
    LocallyBoundedVariationOn (fun t ↦ ∫ u in Ioc 0 t, g u ∂μ) univ := by
  have hp := monotone_integral_Ioc_of_nonneg (fun T ↦ (hg T).pos_part) (fun _ ↦ le_max_right _ _)
  have hn := monotone_integral_Ioc_of_nonneg (fun T ↦ (hg T).neg_part) (fun _ ↦ le_max_right _ _)
  have hv := locallyBoundedVariationOn_sub (hp.monotoneOn univ).locallyBoundedVariationOn
    (hn.monotoneOn univ).locallyBoundedVariationOn
  have heq : (fun t ↦ (∫ u in Ioc 0 t, max (g u) 0 ∂μ) -
      ∫ u in Ioc 0 t, max (-g u) 0 ∂μ) = fun t ↦ ∫ u in Ioc 0 t, g u ∂μ := by
    funext t
    rw [← integral_sub (hg t).pos_part (hg t).neg_part]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : 0 ≤ g u
    · simp only [max_eq_left hu, max_eq_right (neg_nonpos.mpr hu), sub_zero]
    · have hu' : g u ≤ 0 := (lt_of_not_ge hu).le
      simp only [max_eq_right hu', max_eq_left (neg_nonneg.mpr hu'), zero_sub, neg_neg]
  rwa [heq] at hv

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f : ℝ≥0 → ℝ}

theorem isCadlagPath_pathStieltjesIntegral
    (hf : ∀ T, IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure) :
    IsCadlagPath (pathStieltjesIntegral x hx hr f) := by
  have hp := isCadlagPath_integral_Ioc (fun T ↦ integrableOn_positiveVariationStieltjes (hf T))
  have hn := isCadlagPath_integral_Ioc (fun T ↦ integrableOn_negativeVariationStieltjes (hf T))
  have h0 : IsCadlagPath (fun _ : ℝ≥0 ↦ f 0 * x 0) :=
    IsContinuousPath.isCadlagPath continuous_const
  have hneg := hn.continuous_comp (continuous_neg : Continuous (fun r : ℝ ↦ -r))
  have h := h0.add (hp.add hneg)
  change IsCadlagPath (fun t ↦ f 0 * x 0 +
    ((∫ u in Ioc 0 t, f u ∂(positiveVariationStieltjes x hx hr).measure) +
      -(∫ u in Ioc 0 t, f u ∂(negativeVariationStieltjes x hx hr).measure))) at h
  change IsCadlagPath (fun t ↦ f 0 * x 0 +
    ((∫ u in Ioc 0 t, f u ∂(positiveVariationStieltjes x hx hr).measure) -
      (∫ u in Ioc 0 t, f u ∂(negativeVariationStieltjes x hx hr).measure)))
  simpa only [← sub_eq_add_neg] using h

theorem locallyBoundedVariationOn_pathStieltjesIntegral
    (hf : ∀ T, IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure) :
    LocallyBoundedVariationOn (pathStieltjesIntegral x hx hr f) univ := by
  have hp := locallyBoundedVariationOn_integral_Ioc
    (fun T ↦ integrableOn_positiveVariationStieltjes (hf T))
  have hn := locallyBoundedVariationOn_integral_Ioc
    (fun T ↦ integrableOn_negativeVariationStieltjes (hf T))
  have h0 : LocallyBoundedVariationOn (fun _ : ℝ≥0 ↦ f 0 * x 0) univ :=
    (monotone_const.monotoneOn univ).locallyBoundedVariationOn
  exact locallyBoundedVariationOn_add h0 (locallyBoundedVariationOn_sub hp hn)

end StochLean
