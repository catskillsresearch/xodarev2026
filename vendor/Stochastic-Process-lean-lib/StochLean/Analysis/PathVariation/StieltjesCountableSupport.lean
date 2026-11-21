/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesJumpIntegral

/-! # Countably supported FV increment integrals and weighted jump series -/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

theorem measurable_of_locallyBoundedVariation {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) : Measurable x := by
  have hm := ((pathPositiveVariation_monotone hv).measurable.sub
    (pathNegativeVariation_monotone hv).measurable).add_const (x 0)
  simpa only [Pi.sub_apply, pathPositiveVariation_sub_negative, sub_add_cancel] using hm

theorem measurable_leftLim_of_locallyBoundedVariation {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) : Measurable (leftLim x) := by
  have hm := (measurable_of_locallyBoundedVariation hv).sub
    (measurable_jump_of_locallyBoundedVariation hv hr)
  change Measurable (fun t ↦ x t - (x t - leftLim x t)) at hm
  simpa only [sub_sub_cancel] using hm

theorem summable_abs_weighted_jumps_of_locallyBoundedVariation {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T : ℝ≥0)
    {f : ℝ≥0 → ℝ} {C : ℝ} (hC : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ C) :
    Summable (fun t : Ioc 0 T ↦ |f t * (x t - leftLim x t)|) := by
  apply ((summable_abs_jumps_of_locallyBoundedVariation hv hr T).mul_left C).of_norm_bounded
  intro t
  simp only [Real.norm_eq_abs, abs_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC t t.2) (abs_nonneg _)

theorem pathStieltjesIncrementIntegral_eq_tsum_of_countable_support {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T : ℝ≥0)
    {f : ℝ≥0 → ℝ} (hf : Measurable f) (hc : (support f).Countable)
    {C : ℝ} (hC : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ C) :
    pathStieltjesIncrementIntegral x hv hr f 0 T =
      ∑' t : Ioc 0 T, f t * (x t - leftLim x t) := by
  let p := positiveVariationStieltjes x hv hr
  let n := negativeVariationStieltjes x hv hr
  have hi := integrableOn_variationStieltjes_of_bounded (hx := hv) (hr := hr) hf hC
  have hp := summable_stieltjes_atom_mul_of_bounded p T hC
  have hn := summable_stieltjes_atom_mul_of_bounded n T hC
  change (∫ t in Ioc 0 T, f t ∂p.measure) - (∫ t in Ioc 0 T, f t ∂n.measure) = _
  rw [setIntegral_eq_tsum_of_countable_support hc measurableSet_Ioc
      (integrableOn_positiveVariationStieltjes hi),
    setIntegral_eq_tsum_of_countable_support hc measurableSet_Ioc
      (integrableOn_negativeVariationStieltjes hi), ← hp.tsum_sub hn]
  apply tsum_congr
  intro t
  rw [← sub_mul]
  change ((p.measure {(t : ℝ≥0)}).toReal - (n.measure {(t : ℝ≥0)}).toReal) * f t = _
  rw [variationStieltjes_measure_singleton_sub (hx := hv) (hr := hr) t.2.1, mul_comm]

end StochLean
