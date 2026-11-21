/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardPathRegularity
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Continuous actual hazard paths for diffuse lifetime laws

For a finite measure with null singletons, the actual capped hazard is
continuous wherever the cap has positive closed survival mass. The proof
uses dominated convergence along the full neighborhood filter, not merely
right continuity: the moving indicator converges off its single boundary
point, and that point has measure zero. The dominating extended integral
is proved finite before applying `toReal`.

Almost every actual lifetime has positive closed survival and is finite
under the null-singleton hypothesis. On this common event, its original
stopped hazard is the continuous capped hazard at that lifetime. No version
replacement, logarithm identity, or absolute-continuity claim is made.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ] [NullSingletonClass μ]

/-- A diffuse finite lifetime law gives a genuinely continuous real hazard
after a deterministic cap of positive closed survival. -/
theorem continuous_eCumulativeHazard_toReal_min
    (T : ℝ≥0) (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) :
    Continuous (fun t : ℝ≥0 ↦ (eCumulativeHazard μ (min t T)).toReal) := by
  classical
  let w : WithTop ℝ≥0 → ℝ≥0∞ := fun u ↦ (μ (Ici u))⁻¹
  let ν := μ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))
  let f : ℝ≥0 → WithTop ℝ≥0 → ℝ≥0∞ :=
    fun r ↦ (Iic ((min r T : ℝ≥0) : WithTop ℝ≥0)).indicator w
  have hw : Measurable w := by
    have hs : Antitone (fun u : WithTop ℝ≥0 ↦ μ (Ici u)) := by
      intro u v huv
      exact measure_mono (Ici_subset_Ici.mpr huv)
    exact hs.measurable.inv
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
  apply continuous_iff_continuousAt.mpr
  intro t
  have hf : ∀ r, Measurable (f r) := fun _ ↦ hw.indicator measurableSet_Iic
  have hbound : ∀ r, ∀ᵐ u ∂ν, f r u ≤ w u := by
    intro r
    exact ae_of_all _ fun u ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le) u
  have hfin : (∫⁻ u, w u ∂ν) ≠ ∞ :=
    eCumulativeHazard_ne_top_of_le μ hT le_rfl
  have hlim : ∀ᵐ u ∂ν, Tendsto (fun r ↦ f r u) (𝓝 t) (𝓝 (f t u)) := by
    filter_upwards [ν.ae_ne (((min t T : ℝ≥0) : WithTop ℝ≥0))] with u hu
    have hc : Tendsto (fun r : ℝ≥0 ↦ ((min r T : ℝ≥0) : WithTop ℝ≥0))
        (𝓝 t) (𝓝 (((min t T : ℝ≥0) : WithTop ℝ≥0))) :=
      (WithTop.continuous_coe.comp (continuous_id.min continuous_const)).continuousAt
    rcases lt_or_gt_of_ne hu with hlt | hgt
    · have heq : f t u = w u := Set.indicator_of_mem hlt.le w
      rw [heq]
      apply tendsto_const_nhds.congr'
      filter_upwards [hc.eventually (Ioi_mem_nhds hlt)] with r hr
      exact (Set.indicator_of_mem hr.le w).symm
    · have heq : f t u = 0 := Set.indicator_of_notMem
        (show u ∉ Iic ((min t T : ℝ≥0) : WithTop ℝ≥0) from not_le_of_gt hgt) w
      rw [heq]
      apply tendsto_const_nhds.congr'
      filter_upwards [hc.eventually (Iio_mem_nhds hgt)] with r hr
      exact (Set.indicator_of_notMem
        (show u ∉ Iic ((min r T : ℝ≥0) : WithTop ℝ≥0) from not_le_of_gt hr) w).symm
  have hlimH : Tendsto (fun r ↦ eCumulativeHazard μ (min r T))
      (𝓝 t) (𝓝 (eCumulativeHazard μ (min t T))) := by
    simpa only [he] using
      (tendsto_lintegral_filter_of_dominated_convergence w
        (Eventually.of_forall hf) (Eventually.of_forall hbound) hfin hlim)
  exact (ENNReal.tendsto_toReal
    (eCumulativeHazard_ne_top_of_le μ hT (min_le_right t T))).comp hlimH

/-- The original uncapped stopped hazard has continuous paths on one
common event for a finite diffuse lifetime law, without any support guard. -/
theorem hasContinuousPaths_stopped_eCumulativeHazard :
    HasContinuousPaths (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id) μ := by
  filter_upwards [ae_pos_measure_Ici μ, μ.ae_ne ⊤] with v hv hfin
  cases v using WithTop.recTopCoe with
  | top => exact (hfin rfl).elim
  | coe u =>
    change Continuous (fun t ↦ stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t (u : WithTop ℝ≥0))
    simpa only [stoppedProcess, id_eq, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using continuous_eCumulativeHazard_toReal_min μ u hv

end ProbabilityTheory
