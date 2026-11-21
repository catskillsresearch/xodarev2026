/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Oscillation
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Comparison of variation exponents

Klenke 21.59 for continuous deterministic paths. The mesh need only tend to zero;
neither refinement nor a summable rate is imposed. Positive exponents avoid the
unintended convention that a zero increment contributes `0^0 = 1`.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0}

theorem pVariationSum_nonneg (p : ℝ) (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    0 ≤ pVariationSum p π f :=
  sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _

@[simp] theorem pVariationSum_one (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    pVariationSum 1 π f = ∑ i, |π.increment f i| := by
  simp [pVariationSum]

theorem pVariationSum_le_maxIncrement_rpow_mul {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    pVariationSum q π f ≤ (π.maxIncrement f : ℝ) ^ (q - p) * pVariationSum p π f := by
  unfold pVariationSum
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hsplit : |π.increment f i| ^ q =
      |π.increment f i| ^ (q - p) * |π.increment f i| ^ p := by
    rw [← Real.rpow_add' (abs_nonneg _) (show q - p + p ≠ 0 by linarith)]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (abs_nonneg _) (π.abs_increment_le_maxIncrement f i)
      (sub_nonneg.mpr hpq)) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Finite p-variation along the partitions forces zero q-variation for every q > p. -/
theorem HasPVariationAlong.of_exponent_lt {p q a : ℝ} {π : ℕ → TimePartition T}
    {f : ℝ≥0 → ℝ} (hp : 0 < p) (hpq : p < q)
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hvar : HasPVariationAlong p π f a) : HasPVariationAlong q π f 0 := by
  have hpow : Tendsto (fun n ↦ ((π n).maxIncrement f : ℝ) ^ (q - p))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow (sub_pos.mpr hpq).ne'] using
      (Real.continuousAt_rpow_const 0 (q - p) (Or.inr (sub_nonneg.mpr hpq.le))).tendsto.comp
        (TimePartition.maxIncrement_tendsto_zero hf hmesh)
  have hlim := hpow.mul hvar
  rw [zero_mul] at hlim
  exact squeeze_zero (fun n ↦ pVariationSum_nonneg q (π n) f)
    (fun n ↦ pVariationSum_le_maxIncrement_rpow_mul hp hpq.le (π n) f) hlim

/-- The same comparison only needs an eventual bound, not existence of the lower limit. -/
theorem hasPVariationAlong_zero_of_bounded_lower_exponent {p q C : ℝ}
    {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ} (hp : 0 < p) (hpq : p < q)
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, pVariationSum p (π n) f ≤ C) : HasPVariationAlong q π f 0 := by
  have hpow : Tendsto (fun n ↦ ((π n).maxIncrement f : ℝ) ^ (q - p))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow (sub_pos.mpr hpq).ne'] using
      (Real.continuousAt_rpow_const 0 (q - p) (Or.inr (sub_nonneg.mpr hpq.le))).tendsto.comp
        (TimePartition.maxIncrement_tendsto_zero hf hmesh)
  apply squeeze_zero' (Eventually.of_forall fun n ↦ pVariationSum_nonneg q (π n) f) ?_
    (by simpa using hpow.mul_const C)
  filter_upwards [hb] with n hn
  exact (pVariationSum_le_maxIncrement_rpow_mul hp hpq.le (π n) f).trans
    (mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (NNReal.coe_nonneg _) _))

end StochLean
