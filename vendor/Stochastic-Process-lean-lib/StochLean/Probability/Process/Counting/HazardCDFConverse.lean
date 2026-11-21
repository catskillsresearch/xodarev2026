/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardDiffuseCDF

/-! # The exact continuous-CDF domain for an extended lifetime

Continuity of the actual finite-coordinate probability CDF forces its
Stieltjes measure to give zero mass to every singleton. Every original
singleton maps into one of those null fibers, including the infinite point.
Thus continuity is equivalent to null singletons of the original lifetime
law; neither injectivity of the totalized coordinate nor a separate finite-
lifetime premise is needed in this converse.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ]

/-- A continuous actual finite-coordinate CDF rules out all original
lifetime atoms, including any atom at the totalized infinite point. -/
theorem nullSingletonClass_of_continuous_cdf_map_untopA
    (hc : Continuous (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))))) :
    NullSingletonClass μ := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ν := μ.map φ
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  change Continuous (cdf ν) at hc
  constructor
  intro v
  have hzero : ν {φ v} = 0 := by
    rw [← measure_cdf ν, StieltjesFunction.measure_singleton,
      (hc.continuousWithinAt (s := Iic (φ v))).leftLim_eq, sub_self, ENNReal.ofReal_zero]
  have hfiber : μ (φ ⁻¹' {φ v}) = 0 := by
    rw [← Measure.map_apply hφ (measurableSet_singleton (φ v))]
    exact hzero
  apply measure_mono_null ?_ hfiber
  intro w hw
  rcases mem_singleton_iff.mp hw with rfl
  rfl

/-- The source continuous-CDF hypothesis and the verified diffuse lifetime
domain are equivalent for the actual probability pushforward. -/
theorem continuous_cdf_map_untopA_iff :
    Continuous (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))) ↔
      NullSingletonClass μ := by
  refine ⟨nullSingletonClass_of_continuous_cdf_map_untopA μ, fun h ↦ ?_⟩
  let : NullSingletonClass μ := h
  exact continuous_cdf_map_untopA μ

end ProbabilityTheory
