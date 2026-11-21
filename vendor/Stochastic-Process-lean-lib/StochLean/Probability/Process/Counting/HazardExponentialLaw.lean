/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardDiffuseCDF
public import StochLean.Probability.Process.Counting.HazardLogarithm
public import Mathlib.Probability.Distributions.Exponential

/-! # Actual exponential lifetime laws and their cumulative hazards

The only distribution used here is Mathlib's `expMeasure r`. Equality of
the actual real-coordinate pushforward with this law forces the original
extended lifetime measure to have no singleton masses. In particular the
point at infinity has zero mass: its arbitrary totalized finite image cannot
conceal an atom inside an atomless real law.

For positive rate `r`, the pre-jump survival mass is exactly `exp (-r*t)`.
It is positive at every finite time, so the actual cumulative hazard is
finite and its real value is `r*t` by the existing logarithmic formula.
These are source-law consequences, not assumptions about the hazard or a
proposed compensator. The rate is not silently specialized to one.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- An actual atomless exponential pushforward forces every original lifetime
singleton, including zero and infinity, to have zero mass. -/
theorem nullSingletonClass_of_map_untopA_eq_expMeasure
    (μ : Measure (WithTop ℝ≥0)) {r : ℝ}
    (hlaw : μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) = expMeasure r) :
    NullSingletonClass μ := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  let : NullSingletonClass (expMeasure r) := by
    change NullSingletonClass (volume.withDensity (gammaPDF 1 r))
    infer_instance
  change μ.map φ = expMeasure r at hlaw
  constructor
  intro v
  have hzero : μ (φ ⁻¹' {φ v}) = 0 := by
    rw [← Measure.map_apply hφ (measurableSet_singleton (φ v)), hlaw]
    exact measure_singleton _
  apply measure_mono_null ?_ hzero
  intro x hx
  rcases mem_singleton_iff.mp hx with rfl
  rfl

/-- The actual pre-jump survival of an exponential lifetime has its rate-correct
value at every finite nonnegative time. No separate atom hypotheses are needed. -/
theorem measureReal_Ici_of_map_untopA_eq_expMeasure
    (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hlaw : μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) = expMeasure r)
    (t : ℝ≥0) : μ.real (Ici (t : WithTop ℝ≥0)) = Real.exp (-(r * (t : ℝ))) := by
  let : NullSingletonClass μ := nullSingletonClass_of_map_untopA_eq_expMeasure μ hlaw
  have hs := one_sub_cdf_map_untopA_eq_survival μ t
  rw [hlaw, cdf_expMeasure_eq hr (t : ℝ), if_pos t.coe_nonneg] at hs
  linarith

/-- The actual cumulative hazard of an exponential lifetime has slope equal
to its rate. Positive survival is proved from the actual law before `toReal`. -/
theorem eCumulativeHazard_toReal_of_map_untopA_eq_expMeasure
    (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hlaw : μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) = expMeasure r)
    (t : ℝ≥0) : (eCumulativeHazard μ t).toReal = r * (t : ℝ) := by
  let : NullSingletonClass μ := nullSingletonClass_of_map_untopA_eq_expMeasure μ hlaw
  have hs := measureReal_Ici_of_map_untopA_eq_expMeasure μ hr hlaw t
  have hpReal : 0 < μ.real (Ici (t : WithTop ℝ≥0)) := by
    rw [hs]
    exact Real.exp_pos _
  have hp : 0 < μ (Ici (t : WithTop ℝ≥0)) := (ENNReal.toReal_pos_iff.mp hpReal).1
  rw [eCumulativeHazard_toReal_eq_neg_log_survival μ hp, hs, Real.log_exp, neg_neg]

end ProbabilityTheory
