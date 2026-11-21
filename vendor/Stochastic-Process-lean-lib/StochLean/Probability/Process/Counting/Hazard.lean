/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightContinuous
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # The extended cumulative hazard of a lifetime law

The only hazard owner is an ENNReal integral on the original extended
lifetime law. Its denominator is the pre-jump survival mass `μ (Ici u)`,
including an atom at the integration time. The integration interval is
`(0,t]` with finite `t`, so neither an initial atom nor an infinite lifetime
is counted as a finite positive jump.

Real values are used only after proving extended finiteness. Positive
pre-jump survival at `T` controls all earlier hazards and gives a
right-continuous real path after the deterministic cap at `T`. It does
not assert right-continuity of the uncapped real hazard at a terminal
support point with zero survival immediately afterwards.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- The cumulative pre-jump hazard over finite positive lifetimes. Values
remain extended until a survival hypothesis proves their finiteness. -/
noncomputable def eCumulativeHazard (μ : Measure (WithTop ℝ≥0)) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0), (μ (Ici u))⁻¹ ∂μ

variable (μ : Measure (WithTop ℝ≥0))

theorem eCumulativeHazard_zero : eCumulativeHazard μ 0 = 0 := by
  simp only [eCumulativeHazard, WithTop.coe_zero, Ioc_self, Measure.restrict_empty,
    lintegral_zero_measure]

theorem monotone_eCumulativeHazard : Monotone (eCumulativeHazard μ) := by
  intro s t hst
  exact lintegral_mono_set (Ioc_subset_Ioc_right (WithTop.coe_le_coe.mpr hst))

theorem measurable_eCumulativeHazard : Measurable (eCumulativeHazard μ) :=
  (monotone_eCumulativeHazard μ).measurable

/-- An earlier cumulative hazard is bounded by the reciprocal terminal
survival mass times the measure of its actual integration interval. -/
theorem eCumulativeHazard_le_of_le {t T : ℝ≥0} (ht : t ≤ T) :
    eCumulativeHazard μ t ≤ (μ (Ici (T : WithTop ℝ≥0)))⁻¹ *
      μ (Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
  calc
    eCumulativeHazard μ t ≤
        ∫⁻ _ in Ioc (0 : WithTop ℝ≥0) (t : WithTop ℝ≥0),
          (μ (Ici (T : WithTop ℝ≥0)))⁻¹ ∂μ := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro u hu
      apply ENNReal.inv_le_inv.mpr
      exact measure_mono (Ici_subset_Ici.mpr
        (hu.2.trans (WithTop.coe_le_coe.mpr ht)))
    _ = _ := setLIntegral_const _ _

theorem eCumulativeHazard_ne_top_of_le [IsFiniteMeasure μ] {t T : ℝ≥0}
    (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) (ht : t ≤ T) :
    eCumulativeHazard μ t ≠ ∞ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hT.ne') (measure_ne_top μ _))
    (eCumulativeHazard_le_of_le μ ht)

private theorem measurable_hazard_density :
    Measurable (fun u : WithTop ℝ≥0 ↦ (μ (Ici u))⁻¹) := by
  have h : Antitone (fun u : WithTop ℝ≥0 ↦ μ (Ici u)) := by
    intro u v huv
    exact measure_mono (Ici_subset_Ici.mpr huv)
  exact h.measurable.inv

/-- A positive pre-jump survival mass at `T` gives a finite, right-continuous
real cumulative hazard when the observation clock is capped at `T`. -/
theorem isRightContinuousPath_eCumulativeHazard_toReal_min [IsFiniteMeasure μ]
    (T : ℝ≥0) (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) :
    IsRightContinuousPath (fun t : ℝ≥0 ↦ (eCumulativeHazard μ (min t T)).toReal) := by
  classical
  let w : WithTop ℝ≥0 → ℝ≥0∞ := fun u ↦ (μ (Ici u))⁻¹
  let ν := μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))
  let f : ℝ≥0 → WithTop ℝ≥0 → ℝ≥0∞ :=
    fun r ↦ (Iic ((min r T : ℝ≥0) : WithTop ℝ≥0)).indicator w
  have hw : Measurable w := measurable_hazard_density μ
  have he (r : ℝ≥0) : (∫⁻ u, f r u ∂ν) = eCumulativeHazard μ (min r T) := by
    rw [lintegral_indicator measurableSet_Iic]
    change (∫⁻ u, w u ∂(μ.restrict _).restrict _) = _
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hs : Iic ((min r T : ℝ≥0) : WithTop ℝ≥0) ∩
        Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0) =
        Ioc (0 : WithTop ℝ≥0) ((min r T : ℝ≥0) : WithTop ℝ≥0) := by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩,
        fun h ↦ ⟨h.2, h.1, h.2.trans (WithTop.coe_le_coe.mpr (min_le_right r T))⟩⟩
    rw [hs]
    rfl
  intro t
  have hf : ∀ r, Measurable (f r) := fun _ ↦ hw.indicator measurableSet_Iic
  have hbound : ∀ r, ∀ᵐ u ∂ν, f r u ≤ w u := by
    intro r
    exact Eventually.of_forall fun u ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le) u
  have hfin : (∫⁻ u, w u ∂ν) ≠ ∞ :=
    eCumulativeHazard_ne_top_of_le μ hT le_rfl
  have hlim : ∀ᵐ u ∂ν,
      Tendsto (fun r ↦ f r u) (𝓝[≥] t) (𝓝 (f t u)) := by
    apply Eventually.of_forall
    intro u
    by_cases hu : u ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0)
    · have heq : f t u = w u := Set.indicator_of_mem hu w
      rw [heq]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hur : u ≤ ((min r T : ℝ≥0) : WithTop ℝ≥0) :=
        hu.trans (WithTop.coe_le_coe.mpr (min_le_min_right T hr))
      exact (Set.indicator_of_mem hur w).symm
    · have heq : f t u = 0 := Set.indicator_of_notMem hu w
      rw [heq]
      have hc : Tendsto (fun r : ℝ≥0 ↦ ((min r T : ℝ≥0) : WithTop ℝ≥0))
          (𝓝[≥] t) (𝓝 (((min t T : ℝ≥0) : WithTop ℝ≥0))) :=
        (WithTop.continuous_coe.comp (continuous_id.min continuous_const)).continuousWithinAt
      apply tendsto_const_nhds.congr'
      filter_upwards [hc.eventually (Iio_mem_nhds (lt_of_not_ge hu))] with r hr
      have hnot : u ∉ Iic ((min r T : ℝ≥0) : WithTop ℝ≥0) := not_le_of_gt hr
      exact (Set.indicator_of_notMem hnot w).symm
  have hlimH : Tendsto (fun r ↦ eCumulativeHazard μ (min r T))
      (𝓝[≥] t) (𝓝 (eCumulativeHazard μ (min t T))) := by
    simpa only [he] using
      (tendsto_lintegral_filter_of_dominated_convergence w
        (Eventually.of_forall hf) (Eventually.of_forall hbound) hfin hlim)
  exact (ENNReal.tendsto_toReal
    (eCumulativeHazard_ne_top_of_le μ hT (min_le_right t T))).comp hlimH

end ProbabilityTheory
