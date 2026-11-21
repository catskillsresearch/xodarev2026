/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VariationJumpSeries
public import StochLean.ForMathlib.MeasureTheory.CountablySupportedIntegral

/-! # The Stieltjes integral of FV jumps is their squared-jump series

Both Jordan component integrals and both series are genuinely integrable and
summable. The real-valued `tsum` is not used to conceal a divergent series.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

theorem summable_stieltjes_atom_mul_of_bounded (A : StieltjesFunction ℝ≥0)
    (T : ℝ≥0) {f : ℝ≥0 → ℝ} {C : ℝ} (hC : ∀ t ∈ Ioc 0 T, |f t| ≤ C) :
    Summable (fun t : Ioc 0 T ↦ A.measure.real {(t : ℝ≥0)} * f t) := by
  apply ((summable_stieltjes_jumps A T).mul_right C).of_norm_bounded
  intro t
  simp only [norm_mul, Real.norm_eq_abs, measureReal_def, stieltjesMeasure_real_singleton,
    abs_of_nonneg (sub_nonneg.mpr (A.mono.leftLim_le (x := (t : ℝ≥0)) le_rfl))]
  exact mul_le_mul_of_nonneg_left (hC t t.2) (sub_nonneg.mpr (A.mono.leftLim_le le_rfl))

theorem pathStieltjesIncrementIntegral_jump_eq_tsum {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (T : ℝ≥0) :
    pathStieltjesIncrementIntegral x hv hr (fun u ↦ x u - leftLim x u) 0 T =
      ∑' u : Ioc 0 T, (x u - leftLim x u) ^ 2 := by
  let p := positiveVariationStieltjes x hv hr
  let n := negativeVariationStieltjes x hv hr
  let j := fun u ↦ x u - leftLim x u
  have hi := integrableOn_variationStieltjes_jump hv hr T
  have hc := countable_support_jump_of_locallyBoundedVariation hv hr
  have hb : ∀ t ∈ Ioc 0 T, |j t| ≤ ∑' u : Ioc 0 T, |j u| := fun t ht ↦
    abs_jump_le_tsum_abs_jumps hv hr T ⟨t, ht⟩
  have hp := summable_stieltjes_atom_mul_of_bounded p T hb
  have hn := summable_stieltjes_atom_mul_of_bounded n T hb
  change (∫ u in Ioc 0 T, j u ∂p.measure) - (∫ u in Ioc 0 T, j u ∂n.measure) = _
  rw [setIntegral_eq_tsum_of_countable_support hc measurableSet_Ioc
      (integrableOn_positiveVariationStieltjes hi),
    setIntegral_eq_tsum_of_countable_support hc measurableSet_Ioc
      (integrableOn_negativeVariationStieltjes hi), ← hp.tsum_sub hn]
  apply tsum_congr
  intro t
  rw [← sub_mul]
  change ((p.measure {(t : ℝ≥0)}).toReal - (n.measure {(t : ℝ≥0)}).toReal) * j t = _
  rw [variationStieltjes_measure_singleton_sub (hx := hv) (hr := hr) t.2.1]
  exact (pow_two _).symm

end StochLean
