/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardPathRegularity
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Absolutely continuous actual hazard paths from an absolutely continuous law

The input is absolute continuity of the actual finite positive lifetime
measure, pushed to the real line, with respect to Lebesgue measure. The
restriction to `(0,T]` is performed before applying the finite coordinate:
neither an initial atom nor any mass at infinity is moved into that measure.

Positive closed survival at a cap proves that the actual weighted hazard
measure is finite. Its genuine Radon--Nikodym derivative then supplies an
integrable primitive, to which Mathlib's `AbsolutelyContinuousOnInterval`
applies. No density or primitive representing the desired hazard is supplied
as an additional assumption, and no parallel path-regularity predicate is
introduced. Nonnegative-time paths are viewed on a real interval through
`Real.toNNReal`.

On the common event of positive closed survival at the actual lifetime,
this proves local absolute continuity of the original stopped hazard. The
infinite-lifetime case is retained and treated on each finite compact
interval. This is the measure-absolute-continuity formulation; it does not
assert an unproved equivalence with absolute continuity of a CDF function.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

private theorem absolutelyContinuousOnInterval_congr_on
    {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (he : EqOn f g (uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen ↦ ?_⟩
  have hh := hδf E hE hlen
  have hend := hE.1
  have heq : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [he (hend i hi).1, he (hend i hi).2]
  rw [heq]
  exact hh

variable (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ]

/-- If the actual positive lifetime law up to a cap is absolutely continuous
with respect to real Lebesgue measure, its real capped hazard is absolutely
continuous on every compact time interval with positive closed survival at
that cap. The extended weighted integral is proved finite before `toReal`. -/
theorem absolutelyContinuousOnInterval_eCumulativeHazard_toReal_min
    (T : ℝ≥0) (hT : 0 < μ (Ici (T : WithTop ℝ≥0)))
    (hAC : (μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
      (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume) (S : ℝ≥0) :
    AbsolutelyContinuousOnInterval
      (fun x : ℝ ↦ (eCumulativeHazard μ (min x.toNNReal T)).toReal) 0 (S : ℝ) := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ρ := μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))
  let w : WithTop ℝ≥0 → ℝ≥0∞ := fun v ↦ (μ (Ici v))⁻¹
  let κ := (ρ.withDensity w).map φ
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hfin : (∫⁻ v, w v ∂ρ) ≠ ∞ :=
    eCumulativeHazard_ne_top_of_le μ hT le_rfl
  let : IsFiniteMeasure (ρ.withDensity w) := isFiniteMeasure_withDensity hfin
  let : IsFiniteMeasure κ := inferInstance
  have hκAC : κ ≪ volume :=
    ((withDensity_absolutelyContinuous ρ w).map hφ).trans hAC
  have hκmass (r : ℝ≥0) : κ (Ioc (0 : ℝ) (r : ℝ)) =
      eCumulativeHazard μ (min r T) := by
    change ((ρ.withDensity w).map φ) (Ioc (0 : ℝ) (r : ℝ)) = _
    rw [Measure.map_apply hφ measurableSet_Ioc,
      withDensity_apply w (measurableSet_Ioc.preimage hφ)]
    change (∫⁻ v, w v ∂(μ.restrict _).restrict _) = _
    rw [Measure.restrict_restrict (measurableSet_Ioc.preimage hφ)]
    have he : φ ⁻¹' Ioc (0 : ℝ) (r : ℝ) ∩
        Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0) =
        Ioc (0 : WithTop ℝ≥0) ((min r T : ℝ≥0) : WithTop ℝ≥0) := by
      ext v
      cases v using WithTop.recTopCoe with
      | top => simp only [mem_inter_iff, mem_Ioc, WithTop.not_top_le_coe, and_false]
      | coe u =>
          change ((0 < (u : ℝ) ∧ (u : ℝ) ≤ (r : ℝ)) ∧
            ((0 : WithTop ℝ≥0) < (u : WithTop ℝ≥0) ∧
              (u : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0))) ↔
            ((0 : WithTop ℝ≥0) < (u : WithTop ℝ≥0) ∧
              (u : WithTop ℝ≥0) ≤ ((min r T : ℝ≥0) : WithTop ℝ≥0))
          simp only [← NNReal.coe_zero, NNReal.coe_lt_coe, NNReal.coe_le_coe,
            ← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_le_coe, le_min_iff]
          exact ⟨fun h ↦ ⟨h.1.1, h.1.2, h.2.2⟩,
            fun h ↦ ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩⟩
    rw [he]
    rfl
  let f : ℝ → ℝ := fun x ↦ (κ.rnDeriv volume x).toReal
  have hi : Integrable f volume := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := κ) (ν := volume)
        (s := univ) (measure_ne_top κ univ))
  have hprimitive (r : ℝ) (hr : 0 ≤ r) :
      (∫ x in (0 : ℝ)..r, f x) =
        (eCumulativeHazard μ (min r.toNNReal T)).toReal := by
    rw [intervalIntegral.integral_of_le hr]
    calc
      (∫ x in Ioc (0 : ℝ) r, f x) = κ.real (Ioc (0 : ℝ) r) :=
        Measure.setIntegral_toReal_rnDeriv hκAC _
      _ = (eCumulativeHazard μ (min r.toNNReal T)).toReal := by
        have hh := hκmass r.toNNReal
        rw [Real.coe_toNNReal r hr] at hh
        exact congrArg ENNReal.toReal hh
  have hp : AbsolutelyContinuousOnInterval (fun r ↦ ∫ x in (0 : ℝ)..r, f x)
      0 (S : ℝ) :=
    hi.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  apply absolutelyContinuousOnInterval_congr_on hp
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) (S : ℝ) := by
    simpa only [uIcc_of_le S.coe_nonneg] using hr
  exact hprimitive r hr'.1

/-- Absolute continuity of every actual finite positive lifetime restriction
gives local absolute continuity of the original stopped hazard on one common
event. No positive-survival guard, finite-lifetime assumption, or replacement
of the actual process occurs in the conclusion. -/
theorem ae_forall_absolutelyContinuousOnInterval_stopped_eCumulativeHazard
    (hAC : ∀ T : ℝ≥0,
      (μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))).map
        (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume) :
    ∀ᵐ v ∂μ, ∀ S : ℝ≥0, AbsolutelyContinuousOnInterval
      (fun x : ℝ ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id x.toNNReal v)
      0 (S : ℝ) := by
  filter_upwards [ae_pos_measure_Ici μ] with v hv
  cases v using WithTop.recTopCoe with
  | coe u =>
      intro S
      simpa only [stoppedProcess, id_eq, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe] using
        absolutelyContinuousOnInterval_eCumulativeHazard_toReal_min μ u hv (hAC u) S
  | top =>
      intro S
      have hS : 0 < μ (Ici (S : WithTop ℝ≥0)) :=
        hv.trans_le (measure_mono (Ici_subset_Ici.mpr le_top))
      have hp := absolutelyContinuousOnInterval_eCumulativeHazard_toReal_min μ S hS (hAC S) S
      apply absolutelyContinuousOnInterval_congr_on hp
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) (S : ℝ) := by
        simpa only [uIcc_of_le S.coe_nonneg] using hx
      have hxS : x.toNNReal ≤ S :=
        Real.toNNReal_le_iff_le_coe.mpr hx'.2
      simp only [min_eq_left hxS, stoppedProcess, id_eq, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe]

end ProbabilityTheory
