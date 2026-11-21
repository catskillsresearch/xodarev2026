/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardStieltjes
public import StochLean.Probability.Process.Counting.HazardDiffuseCDF
public import StochLean.ForMathlib.MeasureTheory.OrderSurvival
public import StochLean.Analysis.PathVariation.StieltjesLogarithm
public import Mathlib.Probability.Process.Stopping

/-! # The actual logarithmic hazard of a diffuse lifetime law

The original extended hazard is finite at every deterministic time with
positive closed survival. Its real value is the negative logarithm of that
survival. This uses the actual CDF Stieltjes measure and the existing
continuous-path substitution theorem, not a density assumption.

On one common full-measure event, the original stopped hazard consequently
has the source logarithmic CDF formula at all finite observation times.
The lifetime is finite on this event and every stopped survival is positive;
neither `log 0` nor the real conversion of an infinite hazard is used to
interpret the formula. No compensator or process version is reselected.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Before a zero-survival endpoint, a diffuse lifetime's actual finite
cumulative hazard is the negative logarithm of its closed survival mass. -/
theorem eCumulativeHazard_toReal_eq_neg_log_survival {t : ℝ≥0}
    (ht : 0 < μ (Ici (t : WithTop ℝ≥0))) :
    (eCumulativeHazard μ t).toReal = -Real.log (μ.real (Ici (t : WithTop ℝ≥0))) := by
  let ν := μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))
  have hmap : Measurable (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_id.untopA
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hmap.aemeasurable
  have hc : Continuous (cdf ν) := continuous_cdf_map_untopA μ
  have hsurv (u : ℝ≥0) : 1 - cdf ν (u : ℝ) = μ.real (Ici (u : WithTop ℝ≥0)) :=
    one_sub_cdf_map_untopA_eq_survival μ u
  have htReal : 0 < μ.real (Ici (t : WithTop ℝ≥0)) :=
    ENNReal.toReal_pos ht.ne' (measure_ne_top μ _)
  have hFt : cdf ν (t : ℝ) < 1 := sub_pos.mp ((hsurv t).symm ▸ htReal)
  have hF0 : cdf ν 0 = 0 := by
    have h := cdf_map_untopA_eq_lifetime_mass μ (measure_singleton ⊤) 0
    change cdf ν 0 = (μ (Iic (⊥ : WithTop ℝ≥0))).toReal at h
    simpa only [Iic_bot, measure_singleton, ENNReal.toReal_zero] using h
  have hfin : eCumulativeHazard μ t ≠ ∞ :=
    eCumulativeHazard_ne_top_of_le μ ht le_rfl
  have hleft (u : ℝ) : Function.leftLim (cdf ν) u = cdf ν u :=
    (hc.continuousWithinAt (s := Iic u)).leftLim_eq
  have he : eCumulativeHazard μ t =
      ∫⁻ u in Ioc 0 (t : ℝ), ENNReal.ofReal ((1 - cdf ν u)⁻¹) ∂(cdf ν).measure := by
    rw [eCumulativeHazard_eq_lintegral_cdf_measure μ (measure_singleton ⊤)]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro u hu
    change (ENNReal.ofReal (1 - Function.leftLim (cdf ν) u))⁻¹ = _
    rw [hleft]
    exact (ENNReal.ofReal_inv_of_pos
      (sub_pos.mpr (((monotone_cdf ν) hu.2).trans_lt hFt))).symm
  have hactualFinite :
      (∫⁻ u in Ioc 0 (t : ℝ), ENNReal.ofReal ((1 - cdf ν u)⁻¹) ∂(cdf ν).measure) ≠ ∞ :=
    he ▸ hfin
  have hL1 : IntegrableOn (fun u : ℝ ↦ (1 - cdf ν u)⁻¹) (Ioc 0 (t : ℝ))
      (cdf ν).measure := by
    refine ⟨(measurable_const.sub hc.measurable).inv.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [Real.enorm_eq_ofReal (inv_nonneg.mpr
      (sub_nonneg.mpr (cdf_le_one ν _)))] using hactualFinite.lt_top
  have hreal : (eCumulativeHazard μ t).toReal =
      ∫ u in Ioc 0 (t : ℝ), (1 - cdf ν u)⁻¹ ∂(cdf ν).measure := by
    rw [he]
    exact (integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun u ↦ inv_nonneg.mpr (sub_nonneg.mpr (cdf_le_one ν u)))
      hL1.aestronglyMeasurable).symm
  have hlog := StochLean.stieltjesIntegral_real_inv_one_sub_eq_log (cdf ν) hc.continuousOn hFt
  rw [hreal, hlog, hF0, sub_zero, Real.log_one, zero_sub, hsurv t]

/-- On one common full-measure event, every original stopped observation
has the logarithmic CDF formula. No density or deterministic survival guard
is required, since the sampled closed survival is positive almost surely. -/
theorem ae_forall_stopped_eCumulativeHazard_eq_neg_log_cdf :
    ∀ᵐ v ∂μ, ∀ t : ℝ≥0,
      stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v =
        -Real.log (1 - cdf (μ.map (fun w : WithTop ℝ≥0 ↦ (w.untopA : ℝ)))
          (((min (t : WithTop ℝ≥0) v).untopA : ℝ≥0) : ℝ)) := by
  filter_upwards [ae_pos_measure_Ici μ, μ.ae_ne ⊤] with v hv hfinite
  cases v using WithTop.recTopCoe with
  | top => exact (hfinite rfl).elim
  | coe u =>
    intro t
    simp only [stoppedProcess, id_eq, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
    rw [one_sub_cdf_map_untopA_eq_survival]
    exact eCumulativeHazard_toReal_eq_neg_log_survival μ
      (hv.trans_le (measure_mono (Ici_subset_Ici.mpr
        (WithTop.coe_le_coe.mpr (min_le_right t u)))))

end ProbabilityTheory
