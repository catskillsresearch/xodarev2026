/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.MonotoneIntegralMeasure
public import StochLean.Analysis.PathVariation.StieltjesContinuousPart
public import StochLean.Analysis.PathVariation.StieltjesJumpIntegral
public import StochLean.ForMathlib.MeasureTheory.PointAtomicIntegral

/-! # Continuous and jump decomposition of the original Stieltjes integral

The initial term is kept separate from the atom-free continuous part and the
strictly positive-time jump series. The integral is the existing Jordan owner.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

theorem stieltjesIntegral_continuous_jump_decomposition (A : StieltjesFunction ℝ≥0)
    (H : ℝ≥0 → ℝ) (t : ℝ≥0) (hi : IntegrableOn H (Ioc 0 t) A.measure) :
    (∫ s in Ioc 0 t, H s ∂A.measure) =
      (∫ s in Ioc 0 t, H s ∂(stieltjesContinuousPart A).measure) +
        ∑' s : Ioc 0 t, H s * (A s - leftLim A s) := by
  simpa only [stieltjesContinuousPart_measure, measureReal_def,
    stieltjesMeasure_real_singleton, mul_comm] using
    setIntegral_eq_pointDiffusePart_add_tsum measurableSet_Ioc hi

theorem pathStieltjesIntegral_continuous_jump_decomposition (A : StieltjesFunction ℝ≥0)
    (hv : LocallyBoundedVariationOn A univ)
    (hc : LocallyBoundedVariationOn (stieltjesContinuousPart A) univ)
    (H : ℝ≥0 → ℝ) (t : ℝ≥0) (hi : IntegrableOn H (Ioc 0 t) A.measure) :
    pathStieltjesIntegral A hv A.right_continuous H t = H 0 * A 0 +
      pathStieltjesIntegral (stieltjesContinuousPart A) hc
        (stieltjesContinuousPart A).right_continuous H t +
      ∑' s : Ioc 0 t, H s * (A s - leftLim A s) := by
  rw [pathStieltjesIntegral_eq_stieltjesIntegral,
    pathStieltjesIntegral_eq_stieltjesIntegral, stieltjesContinuousPart_zero,
    mul_zero, zero_add, stieltjesIntegral_continuous_jump_decomposition A H t hi]
  exact (add_assoc _ _ _).symm

theorem summable_abs_stieltjes_weighted_jumps_of_bounded (A : StieltjesFunction ℝ≥0)
    (T : ℝ≥0) {H : ℝ≥0 → ℝ} {C : ℝ} (hC : ∀ t ∈ Ioc 0 T, |H t| ≤ C) :
    Summable (fun t : Ioc 0 T ↦ |H t * (A t - leftLim A t)|) := by
  have h := summable_stieltjes_atom_mul_of_bounded A T
    (f := fun t ↦ |H t|) (C := C) (fun t ht ↦ by simpa only [abs_abs] using hC t ht)
  simpa only [measureReal_def, stieltjesMeasure_real_singleton, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr (A.mono.leftLim_le le_rfl)), mul_comm] using h

end StochLean
