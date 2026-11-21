/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CauseSpecificHazard
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Density formulas with the actual observation survival denominator

The density represents the cause measure `ρ` restricted to `(0,T]`,
before the finite lifetime coordinate is mapped to the real line.
The denominator is the closed survival of the observation measure `μ`,
not the survival of `ρ`. Neither independence nor normalization of the
cause measure is assumed.

The ENNReal identity needs no domination or finiteness. For the real
formula, actual domination `ρ ≤ μ` and positive observation survival at
the cap imply finite cause hazard through the existing bound. Only after
this proof do we convert to real values and obtain the actual integrable
density divided by observation survival. Mass at infinity is retained in
the observation denominator and is never moved by the restricted map.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- A density of the actual cause submeasure gives the original extended
cause hazard, with the observation law's closed survival denominator. -/
theorem eCauseSpecificHazard_eq_lintegral_density
    (μ ρ : Measure (WithTop ℝ≥0)) {T : ℝ≥0} {f : ℝ → ℝ}
    (hf : Measurable f)
    (hden : (ρ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
      (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
        (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
          (fun x ↦ ENNReal.ofReal (f x))) {t : ℝ≥0} (ht : t ≤ T) :
    eCauseSpecificHazard μ ρ t =
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
      ∂(ρ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map φ) =
        eCauseSpecificHazard μ ρ t := by
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
    eCauseSpecificHazard μ ρ t =
        ∫⁻ x in Ioc (0 : ℝ) (t : ℝ), q x
          ∂(ρ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map φ :=
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

/-- The density of a genuine cause submeasure, divided by observation
survival, is interval integrable under a positive-survival cap. Its actual
integral equals the real cause hazard, after extended finiteness is proved. -/
theorem intervalIntegrable_cause_density_div_survival_and_integral_eq
    (μ ρ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ] (hρ : ρ ≤ μ)
    {T : ℝ≥0} {f : ℝ → ℝ} (hf : Measurable f)
    (hden : (ρ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
      (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) =
        (volume.restrict (Ioc (0 : ℝ) (T : ℝ))).withDensity
          (fun x ↦ ENNReal.ofReal (f x)))
    (hfn : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)), 0 ≤ f x)
    (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) {t : ℝ≥0} (ht : t ≤ T) :
    IntervalIntegrable (fun x : ℝ ↦ f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0)))
      volume 0 (t : ℝ) ∧
      (∫ x in (0 : ℝ)..(t : ℝ), f x / μ.real (Ici (x.toNNReal : WithTop ℝ≥0))) =
        (eCauseSpecificHazard μ ρ t).toReal := by
  let g : ℝ → ℝ≥0∞ :=
    fun x ↦ ENNReal.ofReal (f x) * (μ (Ici (x.toNNReal : WithTop ℝ≥0)))⁻¹
  have hs : Antitone (fun v : WithTop ℝ≥0 ↦ μ (Ici v)) :=
    fun _ _ huv ↦ measure_mono (Ici_subset_Ici.mpr huv)
  have hg : Measurable g := hf.ennreal_ofReal.mul (hs.measurable.inv.comp
    (WithTop.continuous_coe.comp continuous_real_toNNReal).measurable)
  have he : (∫⁻ x in Ioc (0 : ℝ) (t : ℝ), g x) = eCauseSpecificHazard μ ρ t :=
    (eCauseSpecificHazard_eq_lintegral_density μ ρ hf hden ht).symm
  have hfin : (∫⁻ x in Ioc (0 : ℝ) (t : ℝ), g x) ≠ ∞ := by
    rw [he]
    exact eCauseSpecificHazard_ne_top_of_le μ ρ hρ hT ht
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
    _ = (eCauseSpecificHazard μ ρ t).toReal :=
      (integral_toReal hg.aemeasurable (ae_lt_top' hg.aemeasurable hfin)).trans
        (congrArg ENNReal.toReal he)

end ProbabilityTheory
