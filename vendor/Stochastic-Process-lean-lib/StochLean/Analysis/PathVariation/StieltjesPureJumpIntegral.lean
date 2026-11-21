/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegralDecomposition
public import StochLean.Analysis.PathVariation.StieltjesCountableSupport

/-! # Integrating an actual pure-jump finite-variation path

When a path equals its initial value plus its actual jump series, the
continuous parts of its two canonical Jordan components agree. Their
integrals cancel, leaving the absolutely convergent weighted jump series.
The initial source term is still separate from the positive-time integral.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

variable {x : ℝ≥0 → ℝ} (hv : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

theorem variationStieltjes_continuousParts_eq_of_pureJump
    (hj : ∀ t, x t - x 0 = ∑' s : Ioc 0 t, (x s - leftLim x s)) :
    stieltjesContinuousPart (positiveVariationStieltjes x hv hr) =
      stieltjesContinuousPart (negativeVariationStieltjes x hv hr) := by
  let p := positiveVariationStieltjes x hv hr
  let n := negativeVariationStieltjes x hv hr
  apply StieltjesFunction.ext
  intro t
  have hp := stieltjes_continuous_jump_decomposition p t
  have hn := stieltjes_continuous_jump_decomposition n t
  have hp0 : p 0 = 0 := pathPositiveVariation_zero x
  have hn0 : n 0 = 0 := pathNegativeVariation_zero x
  have hd : p t - n t = x t - x 0 := pathPositiveVariation_sub_negative x t
  have hs : (∑' s : Ioc 0 t, (p s - leftLim p s)) -
      (∑' s : Ioc 0 t, (n s - leftLim n s)) = x t - x 0 := by
    rw [← (summable_stieltjes_jumps p t).tsum_sub (summable_stieltjes_jumps n t), hj t]
    apply tsum_congr
    intro s
    exact variationStieltjes_jump_sub hv hr s.2.1
  change stieltjesContinuousPart p t = stieltjesContinuousPart n t
  linarith only [hp, hn, hp0, hn0, hd, hs]

theorem pathStieltjesIncrementIntegral_eq_tsum_of_pureJump_of_integrable
    (hj : ∀ t, x t - x 0 = ∑' s : Ioc 0 t, (x s - leftLim x s))
    (T : ℝ≥0) {H : ℝ≥0 → ℝ}
    (hi : IntegrableOn H (Ioc 0 T) (totalVariationStieltjes x hv hr).measure)
    {C : ℝ} (hC : ∀ s ∈ Ioc 0 T, ‖H s‖ ≤ C) :
    pathStieltjesIncrementIntegral x hv hr H 0 T =
      ∑' s : Ioc 0 T, H s * (x s - leftLim x s) := by
  let p := positiveVariationStieltjes x hv hr
  let n := negativeVariationStieltjes x hv hr
  have hp := (summable_abs_stieltjes_weighted_jumps_of_bounded p T hC).of_abs
  have hn := (summable_abs_stieltjes_weighted_jumps_of_bounded n T hC).of_abs
  have he : stieltjesContinuousPart p = stieltjesContinuousPart n :=
    variationStieltjes_continuousParts_eq_of_pureJump hv hr hj
  change (∫ s in Ioc 0 T, H s ∂p.measure) - (∫ s in Ioc 0 T, H s ∂n.measure) = _
  rw [stieltjesIntegral_continuous_jump_decomposition p H T
      (integrableOn_positiveVariationStieltjes hi),
    stieltjesIntegral_continuous_jump_decomposition n H T
      (integrableOn_negativeVariationStieltjes hi), he]
  rw [add_sub_add_left_eq_sub, ← hp.tsum_sub hn]
  apply tsum_congr
  intro s
  rw [← mul_sub, variationStieltjes_jump_sub hv hr s.2.1]

theorem pathStieltjesIncrementIntegral_eq_tsum_of_pureJump
    (hj : ∀ t, x t - x 0 = ∑' s : Ioc 0 t, (x s - leftLim x s))
    (T : ℝ≥0) {H : ℝ≥0 → ℝ} (hm : Measurable H)
    {C : ℝ} (hC : ∀ s ∈ Ioc 0 T, ‖H s‖ ≤ C) :
    pathStieltjesIncrementIntegral x hv hr H 0 T =
      ∑' s : Ioc 0 T, H s * (x s - leftLim x s) :=
  pathStieltjesIncrementIntegral_eq_tsum_of_pureJump_of_integrable hv hr hj T
    (integrableOn_variationStieltjes_of_bounded hm hC) hC

theorem pathStieltjesIntegral_eq_initial_add_tsum_of_pureJump
    (hj : ∀ t, x t - x 0 = ∑' s : Ioc 0 t, (x s - leftLim x s))
    (T : ℝ≥0) {H : ℝ≥0 → ℝ} (hm : Measurable H)
    {C : ℝ} (hC : ∀ s ∈ Ioc 0 T, ‖H s‖ ≤ C) :
    pathStieltjesIntegral x hv hr H T = H 0 * x 0 +
      ∑' s : Ioc 0 T, H s * (x s - leftLim x s) := by
  rw [pathStieltjesIntegral, pathStieltjesIncrementIntegral_eq_tsum_of_pureJump hv hr hj T hm hC]

end StochLean
