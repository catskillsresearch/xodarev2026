/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesDSlope
public import StochLean.Analysis.PathVariation.StieltjesCountableSupport
public import StochLean.Analysis.PathVariation.StieltjesJumpSquareLimit
public import StochLean.Analysis.PathVariation.FiniteVariationCadlag

/-! # Protter II.31: C1 change of variables for cadlag finite-variation paths

The differentiated slope integrates exactly. Its difference from the left
derivative is supported on the actual jumps, and integration of this difference
gives the absolutely summable first-order jump remainder series.
-/

@[expose] public section

open MeasureTheory Set Function ProbabilityTheory
open scoped NNReal

namespace StochLean

theorem dslope_sub_deriv_mul_sub (f : ℝ → ℝ) (a b : ℝ) :
    (dslope f a b - deriv f a) * (b - a) = f b - f a - deriv f a * (b - a) := by
  have h := sub_smul_dslope f a b
  simp only [smul_eq_mul] at h
  linear_combination h

theorem countable_support_dslope_sub_deriv {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (f : ℝ → ℝ) :
    (support (fun t ↦ dslope f (leftLim x t) (x t) - deriv f (leftLim x t))).Countable := by
  apply (countable_support_jump_of_locallyBoundedVariation hv hr).mono
  intro t ht hz
  have he : x t = leftLim x t := sub_eq_zero.mp hz
  apply ht
  change dslope f (leftLim x t) (x t) - deriv f (leftLim x t) = 0
  rw [he, dslope_same, sub_self]

theorem integrableOn_variationStieltjes_left_deriv {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (T : ℝ≥0) :
    IntegrableOn (fun t ↦ deriv f (leftLim x t)) (Ioc 0 T)
      (totalVariationStieltjes x hv hx.1).measure := by
  obtain ⟨C, _, hC⟩ := exists_compact_pair_bound_of_cadlag hx T
    (Φ := fun a _ ↦ deriv f a)
    (hf.continuous_deriv_one.comp continuous_fst)
  exact integrableOn_variationStieltjes_of_bounded
    (hf.continuous_deriv_one.measurable.comp
      (measurable_leftLim_of_locallyBoundedVariation hv hx.1))
    (C := C) (fun t ht ↦ hC t ⟨ht.1.le, ht.2⟩)

theorem integrableOn_variationStieltjes_dslope {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (T : ℝ≥0) :
    IntegrableOn (fun t ↦ dslope f (leftLim x t) (x t)) (Ioc 0 T)
      (totalVariationStieltjes x hv hx.1).measure := by
  obtain ⟨C, _, hC⟩ := exists_compact_pair_bound_of_cadlag hx T (continuous_dslope_of_contDiff hf)
  exact integrableOn_variationStieltjes_of_bounded
    ((continuous_dslope_of_contDiff hf).measurable.comp
      ((measurable_leftLim_of_locallyBoundedVariation hv hx.1).prodMk
        (measurable_of_locallyBoundedVariation hv)))
    (C := C) (fun t ht ↦ hC t ⟨ht.1.le, ht.2⟩)

theorem summable_abs_contDiff_jump_remainders {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (T : ℝ≥0) :
    Summable (fun t : Ioc 0 T ↦
      |f (x t) - f (leftLim x t) - deriv f (leftLim x t) * (x t - leftLim x t)|) := by
  obtain ⟨C, _, hC⟩ := exists_compact_pair_bound_of_cadlag hx T
    (Φ := fun a b ↦ dslope f a b - deriv f a)
    ((continuous_dslope_of_contDiff hf).sub (hf.continuous_deriv_one.comp continuous_fst))
  have hs := summable_abs_weighted_jumps_of_locallyBoundedVariation hv hx.1 T
    (C := C) (fun t ht ↦ hC t ⟨ht.1.le, ht.2⟩)
  simpa only [dslope_sub_deriv_mul_sub] using hs

theorem pathStieltjesIncrementIntegral_dslope_sub_deriv {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (T : ℝ≥0) :
    pathStieltjesIncrementIntegral x hv hx.1
      (fun t ↦ dslope f (leftLim x t) (x t) - deriv f (leftLim x t)) 0 T =
      ∑' t : Ioc 0 T,
        (f (x t) - f (leftLim x t) - deriv f (leftLim x t) * (x t - leftLim x t)) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ dslope f p.1 p.2 - deriv f p.1) :=
    (continuous_dslope_of_contDiff hf).sub (hf.continuous_deriv_one.comp continuous_fst)
  obtain ⟨C, _, hC⟩ := exists_compact_pair_bound_of_cadlag hx T
    (Φ := fun a b ↦ dslope f a b - deriv f a) hc
  have hm := hc.measurable.comp
    ((measurable_leftLim_of_locallyBoundedVariation hv hx.1).prodMk
      (measurable_of_locallyBoundedVariation hv))
  have he := pathStieltjesIncrementIntegral_eq_tsum_of_countable_support hv hx.1 T hm
    (countable_support_dslope_sub_deriv hv hx.1 f) (C := C)
      (fun t ht ↦ hC t ⟨ht.1.le, ht.2⟩)
  simpa only [Function.comp_def, dslope_sub_deriv_mul_sub] using he

theorem pathStieltjesIncrementIntegral_contDiff_cadlag {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (T : ℝ≥0) :
    f (x T) - f (x 0) =
      pathStieltjesIncrementIntegral x hv hx.1 (fun t ↦ deriv f (leftLim x t)) 0 T +
        ∑' t : Ioc 0 T,
          (f (x t) - f (leftLim x t) - deriv f (leftLim x t) * (x t - leftLim x t)) := by
  have he := pathStieltjesIncrementIntegral_dslope_sub_deriv hv hx hf T
  rw [pathStieltjesIncrementIntegral_sub
      (integrableOn_variationStieltjes_dslope hv hx hf T)
      (integrableOn_variationStieltjes_left_deriv hv hx hf T),
    pathStieltjesIncrementIntegral_dslope hv hx hf T] at he
  linarith

theorem locallyBoundedVariationOn_contDiff_comp_of_rightContinuous {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    LocallyBoundedVariationOn (f ∘ x) univ :=
  locallyBoundedVariationOn_contDiff_comp_of_cadlag hv
    (isCadlagPath_of_locallyBoundedVariation hv hr) hf

theorem pathStieltjesIncrementIntegral_contDiff_rightContinuous {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (T : ℝ≥0) :
    Summable (fun t : Ioc 0 T ↦
      |f (x t) - f (leftLim x t) - deriv f (leftLim x t) * (x t - leftLim x t)|) ∧
    f (x T) - f (x 0) = pathStieltjesIncrementIntegral x hv hr
      (fun t ↦ deriv f (leftLim x t)) 0 T + ∑' t : Ioc 0 T,
        (f (x t) - f (leftLim x t) - deriv f (leftLim x t) * (x t - leftLim x t)) :=
  ⟨summable_abs_contDiff_jump_remainders hv (isCadlagPath_of_locallyBoundedVariation hv hr) hf T,
    pathStieltjesIncrementIntegral_contDiff_cadlag hv
      (isCadlagPath_of_locallyBoundedVariation hv hr) hf T⟩

end StochLean
