/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Hazard
public import StochLean.Probability.Process.Counting.HazardCDF
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # The actual CDF Stieltjes integral for a finite lifetime law

The original extended cumulative hazard equals the integral against the
native Stieltjes measure of the actual real lifetime CDF. The denominator
is the pre-jump survival `1 - F(u-)`, so a mass at the integration endpoint
is retained. The interval `(0,t]` excludes the original initial atom.

The probability law has zero mass at infinity. Only on this genuine
finite-lifetime event is the totalized real coordinate used to identify
the original interval events. Its arbitrary finite fallback at infinity
is never interpreted as an actual lifetime.

The proof uses `measure_cdf` and the actual set-integral map theorem,
followed by the proved CDF survival identity. The integral and reciprocal
remain ENNReal throughout; no positive-survival condition, finite-hazard
claim, or conversion of an infinite integral to a real value is used.
No new CDF, hazard, or Stieltjes measure owner is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- The original extended hazard is the actual Stieltjes CDF integral
with the pre-jump survival denominator, for an almost-surely finite
nonnegative lifetime probability law. -/
theorem eCumulativeHazard_eq_lintegral_cdf_measure
    (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ]
    (hTop : μ {⊤} = 0) (t : ℝ≥0) :
    eCumulativeHazard μ t =
      ∫⁻ u in Ioc (0 : ℝ) (t : ℝ),
        (ENNReal.ofReal (1 - Function.leftLim
          (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))) u))⁻¹
          ∂(cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))).measure := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ν := μ.map φ
  let q : ℝ → ℝ≥0∞ := fun u ↦ (ENNReal.ofReal (1 - Function.leftLim (cdf ν) u))⁻¹
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hs : Measurable (fun u : ℝ ↦ 1 - Function.leftLim (cdf ν) u) :=
    measurable_const.sub (monotone_cdf ν).leftLim.measurable
  have hq : Measurable q := hs.ennreal_ofReal.inv
  have hfinite : ∀ᵐ v ∂μ, v ≠ ⊤ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hTop
  have hpre : φ ⁻¹' Ioc (0 : ℝ) (t : ℝ) =ᵐ[μ]
      Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    filter_upwards [hfinite] with v hv
    cases v using WithTop.recTopCoe with
    | top => exact (hv rfl).elim
    | coe a =>
        apply propext
        change (0 < (a : ℝ) ∧ (a : ℝ) ≤ (t : ℝ)) ↔
          ((0 : WithTop ℝ≥0) < (a : WithTop ℝ≥0) ∧
            (a : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0))
        simp only [← NNReal.coe_zero, NNReal.coe_lt_coe, NNReal.coe_le_coe,
          ← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_le_coe]
  change eCumulativeHazard μ t = ∫⁻ u in Ioc (0 : ℝ) (t : ℝ), q u ∂(cdf ν).measure
  rw [measure_cdf ν]
  symm
  change (∫⁻ u in Ioc (0 : ℝ) (t : ℝ), q u ∂μ.map φ) = eCumulativeHazard μ t
  rw [setLIntegral_map measurableSet_Ioc hq hφ]
  calc
    (∫⁻ v in φ ⁻¹' Ioc (0 : ℝ) (t : ℝ), q (φ v) ∂μ) =
        ∫⁻ v in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), q (φ v) ∂μ :=
      setLIntegral_congr hpre
    _ = eCumulativeHazard μ t := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro v hv
      cases v using WithTop.recTopCoe with
      | top => exact (WithTop.not_top_le_coe t hv.2).elim
      | coe a =>
          change (ENNReal.ofReal (1 - Function.leftLim (cdf ν) (a : ℝ)))⁻¹ =
            (μ (Ici (a : WithTop ℝ≥0)))⁻¹
          have hsurv : 1 - Function.leftLim (cdf ν) (a : ℝ) =
              μ.real (Ici (a : WithTop ℝ≥0)) :=
            one_sub_leftLim_cdf_map_untopA_eq_survival μ hTop a
          rw [hsurv, ofReal_measureReal]

end ProbabilityTheory
