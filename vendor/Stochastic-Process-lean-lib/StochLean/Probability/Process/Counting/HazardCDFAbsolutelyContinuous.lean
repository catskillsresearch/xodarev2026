/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardAbsolutelyContinuous
public import StochLean.Probability.Process.Counting.HazardCDF
public import StochLean.ForMathlib.MeasureTheory.StieltjesAbsolutelyContinuous

/-! # The source CDF absolute-continuity hypothesis for a lifetime hazard

Absolute continuity of the actual native CDF on a compact interval implies
absolute continuity of the corresponding actual positive lifetime measure.
The proof uses the original derivative/FTC Stieltjes-measure theorem and
true map/restriction identities. No density representation or hazard
regularity certificate is supplied as input.

The lifetime law has zero mass at infinity before its totalized finite
coordinate is interpreted as a real lifetime. The initial atom is excluded
only by the original positive interval `(0,T]`, not by a new assumption.
The already proved measure-AC hazard theorem then gives local absolute
continuity of the original stopped hazard on one common event.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ]

/-- The actual finite positive lifetime measure is absolutely continuous
when its native CDF is absolutely continuous on the corresponding interval. -/
theorem absolutelyContinuous_map_restrict_lifetime_of_cdf
    (hTop : μ {⊤} = 0) (T : ℝ≥0)
    (hAC : AbsolutelyContinuousOnInterval
      (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))) 0 (T : ℝ)) :
    (μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
      (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ν := μ.map φ
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hfinite : ∀ᵐ v ∂μ, v ≠ ⊤ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hTop
  have hpre : φ ⁻¹' Ioc (0 : ℝ) (T : ℝ) =ᵐ[μ]
      Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0) := by
    filter_upwards [hfinite] with v hv
    cases v using WithTop.recTopCoe with
    | top => exact (hv rfl).elim
    | coe a =>
      apply propext
      change (0 < (a : ℝ) ∧ (a : ℝ) ≤ (T : ℝ)) ↔
        ((0 : WithTop ℝ≥0) < (a : WithTop ℝ≥0) ∧
          (a : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0))
      simp only [← NNReal.coe_zero, NNReal.coe_lt_coe, NNReal.coe_le_coe,
        ← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_le_coe]
  have he : ν.restrict (Ioc 0 (T : ℝ)) =
      (μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map φ := by
    change (μ.map φ).restrict (Ioc 0 (T : ℝ)) = _
    rw [Measure.restrict_map hφ measurableSet_Ioc, Measure.restrict_congr_set hpre]
  have h := (cdf ν).restrict_absolutelyContinuous_of_absolutelyContinuousOnInterval hAC
  rw [measure_cdf ν, he] at h
  exact h

/-- Compact-interval absolute continuity of the actual CDF gives locally
absolutely continuous original stopped hazard paths on one common event. -/
theorem ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard_of_cdf
    (hTop : μ {⊤} = 0)
    (hAC : ∀ T : ℝ≥0, AbsolutelyContinuousOnInterval
      (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))) 0 (T : ℝ)) :
    ∀ᵐ v ∂μ, ∀ S : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun x : ℝ ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id x.toNNReal v)
      0 (S : ℝ) :=
  ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard μ
    (fun T ↦ absolutelyContinuous_map_restrict_lifetime_of_cdf μ hTop T (hAC T))

end ProbabilityTheory
