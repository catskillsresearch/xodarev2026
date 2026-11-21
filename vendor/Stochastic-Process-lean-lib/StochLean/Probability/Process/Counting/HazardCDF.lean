/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! # The native probability CDF of an almost-surely finite lifetime

For a probability law on extended nonnegative lifetimes with no mass at
infinity, the actual pushforward by the finite real coordinate has the same
closed lower masses at nonnegative times. Its strict left CDF limit gives
the pre-jump survival mass, including an atom at the observation time.

The condition of zero mass at infinity is essential for this interpretation:
the totalized finite coordinate would otherwise move that mass to an arbitrary
finite value.
The proof compares interval events only on the genuine finite-lifetime
event. It does not treat this fallback value as an actual infinite-time
observation or apply the native probability CDF to a defective restriction.

The CDF and Stieltjes measure owners are Mathlib's existing `cdf` and
`StieltjesFunction.measure`. The identity `measure_cdf` supplies the actual
`dF` measure, so no parallel CDF or measure wrapper is introduced. The
original atom at zero is allowed; at zero the pre-jump survival is one.
General laws with a possible infinite lifetime use the independent extended
cumulative-hazard owner rather than this finite-real specialization.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

private theorem measurable_real_finite_lifetime :
    Measurable (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) :=
  NNReal.continuous_coe.measurable.comp measurable_id.untopA

variable (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ]

/-- At each nonnegative time, the native CDF of the actual real pushforward
is the original closed lifetime mass, provided infinity has zero mass. -/
theorem cdf_map_untopA_eq_lifetime_mass (hTop : μ {⊤} = 0) (u : ℝ≥0) :
    cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))) (u : ℝ) =
      μ.real (Iic (u : WithTop ℝ≥0)) := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  have hφ : Measurable φ := measurable_real_finite_lifetime
  let : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hfinite : ∀ᵐ v ∂μ, v ≠ ⊤ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hTop
  change cdf (μ.map φ) (u : ℝ) = _
  rw [cdf_eq_real, map_measureReal_apply hφ measurableSet_Iic]
  apply measureReal_congr
  filter_upwards [hfinite] with v hv
  cases v using WithTop.recTopCoe with
  | top => exact (hv rfl).elim
  | coe a =>
      apply propext
      change (a : ℝ) ≤ (u : ℝ) ↔ (a : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)
      rw [NNReal.coe_le_coe, WithTop.coe_le_coe]

/-- The pre-jump survival denominator is one minus the strict left CDF
limit, not one minus the CDF at the observation time. Endpoint and initial
atoms are retained through the original closed upper lifetime mass. -/
theorem one_sub_leftLim_cdf_map_untopA_eq_survival (hTop : μ {⊤} = 0) (u : ℝ≥0) :
    1 - Function.leftLim (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))) (u : ℝ) =
      μ.real (Ici (u : WithTop ℝ≥0)) := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ν := μ.map φ
  have hφ : Measurable φ := measurable_real_finite_lifetime
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hfinite : ∀ᵐ v ∂μ, v ≠ ⊤ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hTop
  have hnon : 0 ≤ 1 - Function.leftLim (cdf ν) (u : ℝ) :=
    sub_nonneg.mpr (((monotone_cdf ν).leftLim_le le_rfl).trans (cdf_le_one ν u))
  have hm := StieltjesFunction.measure_Ici (cdf ν) (tendsto_cdf_atTop ν) (u : ℝ)
  rw [measure_cdf ν] at hm
  have hr := congrArg ENNReal.toReal hm
  change ν.real (Ici (u : ℝ)) =
    (ENNReal.ofReal (1 - Function.leftLim (cdf ν) (u : ℝ))).toReal at hr
  rw [ENNReal.toReal_ofReal hnon] at hr
  change 1 - Function.leftLim (cdf ν) (u : ℝ) = _
  calc
    1 - Function.leftLim (cdf ν) (u : ℝ) = ν.real (Ici (u : ℝ)) := hr.symm
    _ = μ.real (φ ⁻¹' Ici (u : ℝ)) := map_measureReal_apply hφ measurableSet_Ici
    _ = μ.real (Ici (u : WithTop ℝ≥0)) := by
      apply measureReal_congr
      filter_upwards [hfinite] with v hv
      cases v using WithTop.recTopCoe with
      | top => exact (hv rfl).elim
      | coe a =>
          apply propext
          change (u : ℝ) ≤ (a : ℝ) ↔ (u : WithTop ℝ≥0) ≤ (a : WithTop ℝ≥0)
          rw [NNReal.coe_le_coe, WithTop.coe_le_coe]

end ProbabilityTheory
