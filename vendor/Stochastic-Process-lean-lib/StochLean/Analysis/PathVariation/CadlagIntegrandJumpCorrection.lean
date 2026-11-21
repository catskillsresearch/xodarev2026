/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CadlagCompositionBounds
public import StochLean.Analysis.PathVariation.StieltjesCountableSupport
public import StochLean.Analysis.PathVariation.StieltjesJumpSquareLimit
public import StochLean.Probability.Process.Path.CadlagLargeJumps
public import StochLean.Probability.Process.Path.CagladMeasurable

/-! # The right-value correction for a cadlag Stieltjes integrand

Both integrals use the existing finite-variation Stieltjes integral, including
its initial product. The integrand need only be cadlag; it need not have finite
variation. Its right-minus-left difference has countable support and is bounded
on compact intervals. The actual Stieltjes atoms therefore give the absolutely
summable positive-time jump correction.

Here `Function.leftLim m 0 = m 0`. Thus the two initial products cancel. This
convention is deliberately distinguished from the source process convention
which assigns zero to the left limit at time zero.
-/

@[expose] public section

open MeasureTheory Set Function ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

private theorem countable_support_cadlag_difference {m : ℝ≥0 → ℝ}
    (hm : IsCadlagPath m) : (support (fun t ↦ m t - leftLim m t)).Countable := by
  have hf (n k : ℕ) :
      {t : ℝ≥0 | 0 < t ∧ t ≤ (n : ℝ≥0) ∧
        1 / (k + 1 : ℝ) < ‖m t - leftLim m t‖}.Finite := by
    apply (hm.finite_large_jumps_Ioc (X := fun t (_ : Unit) ↦ m t) (ω := ())
      (n : ℝ≥0) (b := 1 / (k + 1 : ℝ)) (by positivity)).subset
    rintro t ⟨ht, htn, hj⟩
    refine ⟨ht, htn, ?_⟩
    simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne'] using hj
  apply (Set.countable_iUnion fun n : ℕ ↦
    Set.countable_iUnion fun k : ℕ ↦ (hf n k).countable).mono
  intro t ht
  have hj : m t - leftLim m t ≠ 0 := ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hj (by
      rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le), sub_self])
  obtain ⟨n, hn⟩ := exists_nat_ge t
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hj)
  exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨k, pos_iff_ne_zero.mpr ht0, hn, hk⟩⟩

/-- A real cadlag path and its totalized left-limit path are Borel
measurable. -/
theorem measurable_cadlag_and_leftLim {m : ℝ≥0 → ℝ}
    (hm : IsCadlagPath m) : Measurable m ∧ Measurable (leftLim m) := by
  have hl : IsLeftContinuousPath (leftLim m) := by
    intro t
    by_cases ht : t = 0
    · subst t
      simpa only [show Iic (0 : ℝ≥0) = {0} from Iic_bot] using
        (continuousWithinAt_singleton (f := leftLim m) (x := 0))
    · exact continuousWithinAt_leftLim_Iic (tendsto_leftLim_of_tendsto (hm.2 t ht))
  have hj : Measurable (fun t ↦ m t - leftLim m t) := by
    apply measurable_const.measurable_of_countable_ne (f := fun _ : ℝ≥0 ↦ (0 : ℝ))
    simpa only [ne_comm, support, mem_ofPred_eq] using countable_support_cadlag_difference hm
  refine ⟨?_, hl.measurable⟩
  have he := hj.add hl.measurable
  change Measurable (fun t ↦ (m t - leftLim m t) + leftLim m t) at he
  simpa only [sub_add_cancel] using he

variable {x m : ℝ≥0 → ℝ} (hv : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (hm : IsCadlagPath m) (T : ℝ≥0)

include hv hr hm

/-- Right and left cadlag values are both integrable against the actual
total-variation measure on every finite positive-time interval. -/
theorem integrableOn_variationStieltjes_cadlag_and_leftLim :
    IntegrableOn m (Ioc 0 T) (totalVariationStieltjes x hv hr).measure ∧
      IntegrableOn (leftLim m) (Ioc 0 T) (totalVariationStieltjes x hv hr).measure := by
  obtain ⟨hmm, hml⟩ := measurable_cadlag_and_leftLim hm
  obtain ⟨C, _, hC⟩ := hm.exists_norm_bound_Icc T
  obtain ⟨D, _, hD⟩ := exists_compact_pair_bound_of_cadlag hm T
    (Φ := fun a _ ↦ a) continuous_fst
  exact ⟨integrableOn_variationStieltjes_of_bounded hmm
      (C := C) (fun t ht ↦ hC t ⟨ht.1.le, ht.2⟩),
    integrableOn_variationStieltjes_of_bounded hml
      (C := D) (fun t ht ↦ hD t ⟨ht.1.le, ht.2⟩)⟩

/-- The positive-time jump correction is absolutely summable, without any
variation assumption on the cadlag integrand. -/
theorem summable_abs_cadlag_mixed_jumps :
    Summable (fun t : Ioc 0 T ↦ |(m t - leftLim m t) * (x t - leftLim x t)|) := by
  obtain ⟨C, _, hC⟩ := exists_compact_pair_bound_of_cadlag hm T
    (Φ := fun a b ↦ b - a) (continuous_snd.sub continuous_fst)
  exact summable_abs_weighted_jumps_of_locallyBoundedVariation hv hr T
    (f := fun t ↦ m t - leftLim m t) (C := C)
    (fun t ht ↦ hC t ⟨ht.1.le, ht.2⟩)

/-- Replacing left values by right values in the actual Stieltjes integral
adds precisely the positive-time jump products. The initial product is retained
in each integral and cancels because the native left limit at zero is `m 0`. -/
theorem pathStieltjesIntegral_sub_leftLim_integrand_eq_tsum :
    pathStieltjesIntegral x hv hr m T - pathStieltjesIntegral x hv hr (leftLim m) T =
      ∑' t : Ioc 0 T, (m t - leftLim m t) * (x t - leftLim x t) := by
  obtain ⟨hi, hil⟩ := integrableOn_variationStieltjes_cadlag_and_leftLim hv hr hm T
  obtain ⟨hmm, hml⟩ := measurable_cadlag_and_leftLim hm
  obtain ⟨C, _, hC⟩ := exists_compact_pair_bound_of_cadlag hm T
    (Φ := fun a b ↦ b - a) (continuous_snd.sub continuous_fst)
  have he := pathStieltjesIncrementIntegral_eq_tsum_of_countable_support hv hr T
    (f := fun t ↦ m t - leftLim m t)
    (hmm.sub hml) (countable_support_cadlag_difference hm)
    (C := C) (fun t ht ↦ hC t ⟨ht.1.le, ht.2⟩)
  rw [pathStieltjesIncrementIntegral_sub hi hil] at he
  simpa only [pathStieltjesIntegral,
    leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le),
    add_sub_add_left_eq_sub] using he

end StochLean
