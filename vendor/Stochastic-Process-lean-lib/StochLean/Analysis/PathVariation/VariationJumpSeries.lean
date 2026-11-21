/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegralJump
public import StochLean.Analysis.PathVariation.StieltjesJumpSum
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Countable support and absolute summability of FV jumps

The actual positive and negative Stieltjes measures control the jumps. No
enumeration of jumps or summability assumption is supplied by the caller.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

variable {x : ℝ≥0 → ℝ} (hv : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

include hv hr

theorem variationStieltjes_jump_sub {t : ℝ≥0} (ht : 0 < t) :
    (positiveVariationStieltjes x hv hr t - leftLim (positiveVariationStieltjes x hv hr) t) -
      (negativeVariationStieltjes x hv hr t - leftLim (negativeVariationStieltjes x hv hr) t) =
      x t - leftLim x t := by
  simpa only [stieltjesMeasure_real_singleton] using
    (variationStieltjes_measure_singleton_sub (hx := hv) (hr := hr) ht)

theorem countable_support_jump_of_locallyBoundedVariation :
    (support (fun t ↦ x t - leftLim x t)).Countable := by
  let p := positiveVariationStieltjes x hv hr
  let n := negativeVariationStieltjes x hv hr
  apply ((countable_pointAtomSet p.measure).union (countable_pointAtomSet n.measure)).mono
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact False.elim (ht (by
      change x 0 - leftLim x 0 = 0
      rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le), sub_self]))
  · by_contra h
    have hz : p.measure {t} = 0 ∧ n.measure {t} = 0 := by
      simpa only [mem_union, pointAtomSet, mem_ofPred_eq, not_or, not_not] using h
    have he := variationStieltjes_measure_singleton_sub (hx := hv) (hr := hr)
      (pos_iff_ne_zero.mpr ht0)
    change (p.measure {t}).toReal - (n.measure {t}).toReal = x t - leftLim x t at he
    rw [hz.1, hz.2, ENNReal.toReal_zero, sub_self] at he
    exact ht he.symm

theorem measurable_jump_of_locallyBoundedVariation :
    Measurable (fun t ↦ x t - leftLim x t) := by
  apply measurable_const.measurable_of_countable_ne (f := fun _ : ℝ≥0 ↦ (0 : ℝ))
  simpa only [ne_comm, support, mem_ofPred_eq] using
    countable_support_jump_of_locallyBoundedVariation hv hr

theorem summable_abs_jumps_of_locallyBoundedVariation (T : ℝ≥0) :
    Summable (fun t : Ioc 0 T ↦ |x t - leftLim x t|) := by
  let p := positiveVariationStieltjes x hv hr
  let n := negativeVariationStieltjes x hv hr
  apply ((summable_stieltjes_jumps p T).add (summable_stieltjes_jumps n T)).of_norm_bounded
  intro t
  rw [Real.norm_eq_abs, abs_abs, ← variationStieltjes_jump_sub hv hr t.2.1]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (p.mono.leftLim_le le_rfl)),
    abs_of_nonneg (sub_nonneg.mpr (n.mono.leftLim_le le_rfl))] using
      norm_sub_le (p t - leftLim p t) (n t - leftLim n t)

theorem abs_jump_le_tsum_abs_jumps (T : ℝ≥0) (t : Ioc 0 T) :
    |x t - leftLim x t| ≤ ∑' s : Ioc 0 T, |x s - leftLim x s| := by
  have h := (summable_abs_jumps_of_locallyBoundedVariation hv hr T).sum_le_tsum
    {t} (fun _ _ ↦ abs_nonneg _)
  simpa only [Finset.sum_singleton] using h

theorem summable_sq_jumps_of_locallyBoundedVariation (T : ℝ≥0) :
    Summable (fun t : Ioc 0 T ↦ (x t - leftLim x t) ^ 2) := by
  let C := ∑' s : Ioc 0 T, |x s - leftLim x s|
  apply ((summable_abs_jumps_of_locallyBoundedVariation hv hr T).mul_left C).of_norm_bounded
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs, pow_two]
  exact mul_le_mul_of_nonneg_right (abs_jump_le_tsum_abs_jumps hv hr T t) (abs_nonneg _)

theorem integrableOn_variationStieltjes_jump (T : ℝ≥0) :
    IntegrableOn (fun t ↦ x t - leftLim x t) (Ioc 0 T)
      (totalVariationStieltjes x hv hr).measure := by
  apply integrableOn_variationStieltjes_of_bounded
    (measurable_jump_of_locallyBoundedVariation hv hr)
    (C := ∑' s : Ioc 0 T, |x s - leftLim x s|)
  intro t ht
  exact abs_jump_le_tsum_abs_jumps hv hr T ⟨t, ht⟩

end StochLean
