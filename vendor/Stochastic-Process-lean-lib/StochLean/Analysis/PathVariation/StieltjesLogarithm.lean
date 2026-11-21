/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.C1ChangeOfVariables
public import StochLean.Analysis.PathVariation.MonotoneIntegralMeasure
public import StochLean.ForMathlib.MeasureTheory.StieltjesNNRealRestriction
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The logarithmic integral along a continuous Stieltjes function

On a compact interval where the increasing path remains strictly below one,
its actual Stieltjes integral of the reciprocal survival is the logarithmic
survival difference. No density with respect to time is required, so the
formula also applies to singular continuous Stieltjes functions.

The existing pathwise substitution theorem supplies the change of variables.
A globally continuous capped reciprocal agrees with the true reciprocal on
the entire relevant range; no differentiability at its pole is assumed.
The original initial value is retained, and no formula is claimed at a
zero-survival endpoint, where the extended integral may be infinite.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace StochLean

/-- The actual continuous-law Stieltjes hazard integral is the logarithmic
survival difference, with its initial value and positive-survival domain. -/
theorem stieltjesIntegral_inv_one_sub_eq_log (A : StieltjesFunction ℝ≥0) {T : ℝ≥0}
    (hA : ContinuousOn A (Icc 0 T)) (hT : A T < 1) :
    (∫ u in Ioc 0 T, (1 - A u)⁻¹ ∂A.measure) =
      Real.log (1 - A 0) - Real.log (1 - A T) := by
  let g : ℝ → ℝ := fun z ↦ (1 - min z (A T))⁻¹
  have hg : Continuous g :=
    (continuous_const.sub (continuous_id.min continuous_const)).inv₀
      (fun z ↦ (sub_pos.mpr ((min_le_right z (A T)).trans_lt hT)).ne')
  have hv : LocallyBoundedVariationOn A univ :=
    (A.mono.monotoneOn univ).locallyBoundedVariationOn
  have h0T : A 0 ≤ A T := A.mono bot_le
  have h0 : 0 < 1 - A 0 := sub_pos.mpr (h0T.trans_lt hT)
  have hpos : 0 < 1 - A T := sub_pos.mpr hT
  calc
    (∫ u in Ioc 0 T, (1 - A u)⁻¹ ∂A.measure) =
        ∫ u in Ioc 0 T, g (A u) ∂A.measure := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only [g]
      rw [min_eq_left (A.mono hu.2)]
    _ = pathStieltjesIncrementIntegral A hv A.right_continuous (fun u ↦ g (A u)) 0 T :=
      (pathStieltjesIncrementIntegral_eq_stieltjesIntegral A hv _ 0 T).symm
    _ = ∫ z in A 0..A T, g z := pathStieltjesIncrementIntegral_substitution hA hg
    _ = ∫ z in A 0..A T, (1 - z)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le h0T] at hz
      dsimp only [g]
      rw [min_eq_left hz.2]
    _ = ∫ z in (1 - A T)..(1 - A 0), z⁻¹ :=
      intervalIntegral.integral_comp_sub_left (fun z : ℝ ↦ z⁻¹) 1
    _ = Real.log ((1 - A 0) / (1 - A T)) := integral_inv_of_pos hpos h0
    _ = _ := Real.log_div h0.ne' hpos.ne'

/-- The same actual logarithmic integral on the real time axis. The native
Stieltjes measure is restricted only to the interval `(0,T]`, so an atom or
nonzero value at zero remains in the initial logarithm. -/
theorem stieltjesIntegral_real_inv_one_sub_eq_log (F : StieltjesFunction ℝ) {T : ℝ≥0}
    (hF : ContinuousOn F (Icc 0 (T : ℝ))) (hT : F (T : ℝ) < 1) :
    (∫ u in Ioc 0 (T : ℝ), (1 - F u)⁻¹ ∂F.measure) =
      Real.log (1 - F 0) - Real.log (1 - F (T : ℝ)) := by
  let A : StieltjesFunction ℝ≥0 :=
    ⟨fun t ↦ F (t : ℝ), fun _ _ h ↦ F.mono (NNReal.coe_le_coe.mpr h),
      fun t ↦ (F.right_continuous (t : ℝ)).comp NNReal.continuous_coe.continuousWithinAt
        (fun _ h ↦ NNReal.coe_le_coe.mpr h)⟩
  have hA : ContinuousOn A (Icc 0 T) :=
    hF.comp NNReal.continuous_coe.continuousOn
      (fun u hu ↦ ⟨u.coe_nonneg, NNReal.coe_le_coe.mpr hu.2⟩)
  have hm := A.measure_map_nnreal_eq_restrict F (fun _ ↦ rfl)
  have hp : (fun t : ℝ≥0 ↦ (t : ℝ)) ⁻¹' Ioc 0 (T : ℝ) = Ioc 0 T := by
    ext u
    change (0 < (u : ℝ) ∧ (u : ℝ) ≤ (T : ℝ)) ↔ (0 < u ∧ u ≤ T)
    simp only [← NNReal.coe_zero, NNReal.coe_lt_coe, NNReal.coe_le_coe]
  calc
    (∫ u in Ioc 0 (T : ℝ), (1 - F u)⁻¹ ∂F.measure) =
        ∫ u in Ioc 0 (T : ℝ), (1 - F u)⁻¹ ∂F.measure.restrict (Ioi 0) := by
      rw [Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (fun _ h ↦ h.1)]
    _ = ∫ u in Ioc 0 (T : ℝ), (1 - F u)⁻¹
        ∂A.measure.map (fun t : ℝ≥0 ↦ (t : ℝ)) := by rw [hm]
    _ = ∫ t in Ioc 0 T, (1 - A t)⁻¹ ∂A.measure := by
      rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.setIntegral_map, hp]
    _ = _ := stieltjesIntegral_inv_one_sub_eq_log A hA hT

end StochLean
