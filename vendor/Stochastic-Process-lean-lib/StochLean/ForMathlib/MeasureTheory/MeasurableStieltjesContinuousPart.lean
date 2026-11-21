/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesContinuousPart
public import StochLean.ForMathlib.MeasureTheory.MeasurablePointDiffusePart
public import StochLean.ForMathlib.MeasureTheory.PointDiffuseRestriction

/-! # The continuous component is measurable from the path up to that time

Only the finite restriction through the requested time is used. This is the
nonanticipation bridge needed for adapted continuous quadratic variation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace StochLean

theorem measurable_stieltjesContinuousPart_of_measurable_upTo
    {Ω : Type*} [MeasurableSpace Ω] {B : Ω → StieltjesFunction ℝ≥0} (T : ℝ≥0)
    (hB : ∀ t ≤ T, Measurable fun ω ↦ B ω t) :
    Measurable fun ω ↦ stieltjesContinuousPart (B ω) T := by
  let κ : Kernel Ω ℝ≥0 := ⟨fun ω ↦ (B ω).measure.restrict (Iic T),
    measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo T hB⟩
  have hκ (ω : Ω) : IsFiniteMeasure (κ ω) := by
    refine ⟨?_⟩
    change ((B ω).measure.restrict (Iic T)) univ < ∞
    rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
    exact ENNReal.ofReal_lt_top
  have h := ENNReal.measurable_toReal.comp
    ((Measure.measurable_coe MeasurableSet.univ).comp
      (measurable_pointDiffusePart_of_finite_fibers κ hκ))
  have heq (ω : Ω) : ((pointDiffusePart (κ ω)) univ).toReal =
      stieltjesContinuousPart (B ω) T := by
    change (pointDiffusePart ((B ω).measure.restrict (Iic T))).real univ = _
    rw [pointDiffusePart_restrict _ measurableSet_Iic, measureReal_restrict_apply_univ]
    rfl
  simpa only [Function.comp_def, heq] using h

end StochLean
