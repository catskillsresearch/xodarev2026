/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! # A symmetric non-integrable random variable with no singleton atoms

On the uniform probability space `(-1,1)`, take `value x = x⁻¹`, with the
standard real inverse convention at zero. Reflection preserves the actual
sample measure, and the resulting law equals the law of the negative value.
The first absolute moment is infinite, as restriction to `(0,1)` gives the
non-integrable power `x^(-1)`. Each singleton of the law has zero mass because
inversion is an involution on all real numbers, including zero.

These are concrete distributional data for Protter's second example on
printed page 128. No filtration, stochastic process, density or CDF selector
is introduced here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean.SymmetricInverseModel

/-- The uniform probability measure on the open symmetric interval. -/
noncomputable def sampleMeasure : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • volume.restrict (Ioo (-1 : ℝ) 1)

instance instIsProbabilityMeasureSampleMeasure : IsProbabilityMeasure sampleMeasure := by
  constructor
  norm_num [sampleMeasure, Measure.smul_apply, Real.volume_Ioo]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Inversion is defined at every sample, with `value 0 = 0`. -/
noncomputable def value (x : ℝ) : ℝ := x⁻¹

theorem measurable_value : Measurable value := measurable_inv

/-- Reflection preserves the actual probability measure, without augmentation. -/
theorem measurePreserving_neg :
    MeasurePreserving (fun x : ℝ ↦ -x) sampleMeasure sampleMeasure := by
  have hs : (fun x : ℝ ↦ -x) ⁻¹' Ioo (-1 : ℝ) 1 = Ioo (-1 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hr := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Ioo (-1 : ℝ) 1) measurableSet_Ioo
  rw [hs] at hr
  exact hr.smul_measure (1 / 2 : ℝ≥0∞)

/-- The actual value and its negative have the same pushforward law. -/
theorem map_neg_value_eq_map_value :
    sampleMeasure.map (fun x ↦ -value x) = sampleMeasure.map value := by
  calc
    sampleMeasure.map (fun x ↦ -value x) =
        sampleMeasure.map (value ∘ fun x : ℝ ↦ -x) := by
      congr 1
      funext x
      simp only [Function.comp_apply, value, inv_neg]
    _ = (sampleMeasure.map (fun x : ℝ ↦ -x)).map value :=
      (Measure.map_map measurable_value measurable_neg).symm
    _ = sampleMeasure.map value := by rw [measurePreserving_neg.map_eq]

theorem not_integrable_value : ¬ Integrable value sampleMeasure := by
  intro h
  have hi : IntegrableOn value (Ioo (-1 : ℝ) 1) :=
    (integrable_smul_measure (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞)).mp h
  have hs : Ioo (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 1 :=
    Ioo_subset_Ioo (by norm_num) le_rfl
  have hp : IntegrableOn (fun x : ℝ ↦ x ^ (-1 : ℝ)) (Ioo (0 : ℝ) 1) := by
    have hi' : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioo (0 : ℝ) 1) := hi.mono hs le_rfl
    simpa only [Real.rpow_neg_one] using hi'
  have hf := (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by
    norm_num)).mp hp
  exact (lt_irrefl (-1 : ℝ)) hf

/-- The absolute first moment is genuinely infinite as an extended integral. -/
theorem lintegral_abs_value_eq_top :
    ∫⁻ x, ENNReal.ofReal |value x| ∂sampleMeasure = ∞ := by
  by_contra h
  apply not_integrable_value
  refine ⟨measurable_value.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_norm value).mpr
  simpa only [Real.norm_eq_abs] using (lt_top_iff_ne_top.mpr h)

/-- The law has no singleton atoms, including at zero. -/
theorem law_singleton_eq_zero (y : ℝ) : (sampleMeasure.map value) {y} = 0 := by
  rw [Measure.map_apply measurable_value (measurableSet_singleton y)]
  have he : value ⁻¹' {y} = {y⁻¹} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, value, inv_eq_iff_eq_inv]
  rw [he]
  simp only [sampleMeasure, Measure.smul_apply, measure_singleton, smul_eq_mul, mul_zero]

end StochLean.SymmetricInverseModel
