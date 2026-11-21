/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Hazard
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The actual density divided by survival formula for cumulative hazard

The density assumption concerns the original lifetime law restricted to
the finite positive interval `(0,T]`, before its finite coordinate is
mapped to the real line. It is an equality of actual measures, not a
supplied formula for the hazard. Initial atoms and mass at infinity are
allowed; the closed survival denominator still uses the original law.

First the original ENNReal hazard is identified with the weighted
Lebesgue integral. For a finite law with positive closed survival at the
cap, the existing hazard bound proves this integral finite. Only then do
we pass to real values and prove that the actual density divided by real
survival is interval integrable and has the required integral.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- A density of the actual finite positive lifetime law gives the original
extended hazard as the Lebesgue integral of density times inverse closed
survival. No finiteness of the law or positive survival is needed here. -/
theorem eCumulativeHazard_eq_lintegral_density
    (μ : Measure (WithTop ℝ≥0)) {T : ℝ≥0} {f : ℝ → ℝ}
    (hf : Measurable f)
    (hden : (μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
      (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
        (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
          (fun x ↦ ENNReal.ofReal (f x))) {t : ℝ≥0} (ht : t ≤ T) :
    eCumulativeHazard μ t =
      ∫⁻ x in Ioc (0 : ℝ) (t : ℝ),
        ENNReal.ofReal (f x) * (μ (Ici (x.toNNReal : WithTop ℝ≥0)))⁻¹ := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let q : ℝ → ℝ≥0∞ := fun x ↦ (μ (Ici (x.toNNReal : WithTop ℝ≥0)))⁻¹
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hs : Antitone (fun v : WithTop ℝ≥0 ↦ μ (Ici v)) :=
    fun _ _ huv ↦ measure_mono (Ici_subset_Ici.mpr huv)
  have hq : Measurable q := hs.measurable.inv.comp
    (WithTop.continuous_coe.comp continuous_real_toNNReal).measurable
  have hpre : φ ⁻¹' Ioc (0 : ℝ) (t : ℝ) ∩
      Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0) =
        Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    ext v
    cases v using WithTop.recTopCoe with
    | top =>
        simp only [mem_inter_iff, mem_preimage, mem_Ioc,
          WithTop.not_top_le_coe, and_false]
    | coe a =>
        change ((0 < (a : ℝ) ∧ (a : ℝ) ≤ (t : ℝ)) ∧
          ((0 : WithTop ℝ≥0) < (a : WithTop ℝ≥0) ∧
            (a : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0))) ↔
          ((0 : WithTop ℝ≥0) < (a : WithTop ℝ≥0) ∧
            (a : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0))
        simp only [← NNReal.coe_zero, NNReal.coe_lt_coe, NNReal.coe_le_coe,
          ← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_le_coe]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.1, h.2.trans ht⟩⟩
  have hpush : (∫⁻ x in Ioc (0 : ℝ) (t : ℝ), q x
      ∂(μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map φ) =
        eCumulativeHazard μ t := by
    rw [setLIntegral_map measurableSet_Ioc hq hφ,
      Measure.restrict_restrict (hφ measurableSet_Ioc), hpre]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro v hv
    cases v using WithTop.recTopCoe with
    | top => exact (WithTop.not_top_le_coe t hv.2).elim
    | coe a =>
        change (μ (Ici ((a : ℝ).toNNReal : WithTop ℝ≥0)))⁻¹ =
          (μ (Ici (a : WithTop ℝ≥0)))⁻¹
        rw [Real.toNNReal_coe]
  calc
    eCumulativeHazard μ t =
        ∫⁻ x in Ioc (0 : ℝ) (t : ℝ), q x
          ∂(μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map φ :=
      hpush.symm
    _ = ∫⁻ x in Ioc (0 : ℝ) (t : ℝ), q x
        ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
          (fun x ↦ ENNReal.ofReal (f x)) := by rw [hden]
    _ = ∫⁻ x in Ioc (0 : ℝ) (t : ℝ), ENNReal.ofReal (f x) * q x
        ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)) :=
      setLIntegral_withDensity_eq_setLIntegral_mul _ hf.ennreal_ofReal hq measurableSet_Ioc
    _ = _ := by
      rw [Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr ht))]

/-- Under positive closed survival at the cap, the actual density divided
by real survival is interval integrable, and its integral is the real
cumulative hazard. Extended finiteness is established before conversion. -/
theorem intervalIntegrable_density_div_survival_and_integral_eq
    (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ] {T : ℝ≥0} {f : ℝ → ℝ}
    (hf : Measurable f)
    (hden : (μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
      (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
        (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
          (fun x ↦ ENNReal.ofReal (f x)))
    (hfn : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)), 0 ≤ f x)
    (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) {t : ℝ≥0} (ht : t ≤ T) :
    IntervalIntegrable (fun x : ℝ ↦ f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0)))
      volume 0 (t : ℝ) ∧
      (∫ x in (0 : ℝ)..(t : ℝ), f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0))) =
        (eCumulativeHazard μ t).toReal := by
  let g : ℝ → ℝ≥0∞ :=
    fun x ↦ ENNReal.ofReal (f x) * (μ (Ici (x.toNNReal : WithTop ℝ≥0)))⁻¹
  have hs : Antitone (fun v : WithTop ℝ≥0 ↦ μ (Ici v)) :=
    fun _ _ huv ↦ measure_mono (Ici_subset_Ici.mpr huv)
  have hg : Measurable g := hf.ennreal_ofReal.mul (hs.measurable.inv.comp
    (WithTop.continuous_coe.comp continuous_real_toNNReal).measurable)
  have he : (∫⁻ x in Ioc (0 : ℝ) (t : ℝ), g x) = eCumulativeHazard μ t :=
    (eCumulativeHazard_eq_lintegral_density μ hf hden ht).symm
  have hfin : (∫⁻ x in Ioc (0 : ℝ) (t : ℝ), g x) ≠ ∞ := by
    rw [he]
    exact eCumulativeHazard_ne_top_of_le μ hT ht
  have hn : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (t : ℝ)), 0 ≤ f x :=
    ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr ht)) hfn
  have heq : (fun x ↦ (g x).toReal) =ᵐ[volume.restrict (Ioc (0 : ℝ) (t : ℝ))]
      (fun x ↦ f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0))) := by
    filter_upwards [hn] with x hx
    simp only [g, ENNReal.toReal_mul, ENNReal.toReal_ofReal hx, ENNReal.toReal_inv,
      measureReal_def, div_eq_mul_inv]
  have hi : Integrable (fun x ↦ (g x).toReal)
      (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfin
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le t.2).2 (hi.congr heq), ?_⟩
  calc
    (∫ x in (0 : ℝ)..(t : ℝ), f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0))) =
        ∫ x in Ioc (0 : ℝ) (t : ℝ), f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0)) :=
      intervalIntegral.integral_of_le t.2
    _ = ∫ x in Ioc (0 : ℝ) (t : ℝ), (g x).toReal := integral_congr_ae heq.symm
    _ = (eCumulativeHazard μ t).toReal :=
      (integral_toReal hg.aemeasurable (ae_lt_top' hg.aemeasurable hfin)).trans
        (congrArg ENNReal.toReal he)

end ProbabilityTheory
