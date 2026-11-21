/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CauseSpecificHazard
public import StochLean.Probability.Process.Counting.HazardPathRegularity

/-! # Actual stopped cause-hazard path regularity

The integration measure is the actual cause submeasure, not the observation
law. Domination supplies the finite hazard bound at positive observation
survival. Dominated convergence for that cause integral gives right continuity;
monotonicity gives finite left limits. At almost every observation lifetime
the same event proves finiteness and cadlag monotone paths for all times.

An infinite lifetime with positive mass is treated at each finite cap.
No infinite clock is evaluated and no null support endpoint is interpreted
through the totalized real value of an infinite hazard. No replacement path
or additional hazard owner is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ ρ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ]

/-- Positive observation survival at a cap yields right continuity of the
actual real cause hazard capped there. -/
theorem isRightContinuousPath_eCauseSpecificHazard_toReal_min
    (hρ : ρ ≤ μ)
    (T : ℝ≥0) (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) :
    IsRightContinuousPath (fun t : ℝ≥0 ↦ (eCauseSpecificHazard μ ρ (min t T)).toReal) := by
  classical
  let w : WithTop ℝ≥0 → ℝ≥0∞ := fun u ↦ (μ (Ici u))⁻¹
  let ν := ρ.restrict (Ioc (0 : WithTop ℝ≥0) (T : WithTop ℝ≥0))
  let f : ℝ≥0 → WithTop ℝ≥0 → ℝ≥0∞ :=
    fun r ↦ (Iic ((min r T : ℝ≥0) : WithTop ℝ≥0)).indicator w
  have hw : Measurable w := by
    have ha : Antitone (fun u : WithTop ℝ≥0 ↦ μ (Ici u)) :=
      fun _ _ huv ↦ measure_mono (Ici_subset_Ici.mpr huv)
    exact ha.measurable.inv
  have he (r : ℝ≥0) : (∫⁻ u, f r u ∂ν) = eCauseSpecificHazard μ ρ (min r T) := by
    rw [lintegral_indicator measurableSet_Iic]
    change (∫⁻ u, w u ∂(ρ.restrict _).restrict _) = _
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
    eCauseSpecificHazard_ne_top_of_le μ ρ hρ hT le_rfl
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
  have hlimH : Tendsto (fun r ↦ eCauseSpecificHazard μ ρ (min r T))
      (𝓝[≥] t) (𝓝 (eCauseSpecificHazard μ ρ (min t T))) := by
    simpa only [he] using
      (tendsto_lintegral_filter_of_dominated_convergence w
        (Eventually.of_forall hf) (Eventually.of_forall hbound) hfin hlim)
  exact (ENNReal.tendsto_toReal
    (eCauseSpecificHazard_ne_top_of_le μ ρ hρ hT (min_le_right t T))).comp hlimH


/-- At a lifetime with positive observation survival, all stopped cause
hazards are finite and their real path is monotone and cadlag. -/
theorem stopped_eCauseSpecificHazard_paths_of_positive_survival (hρ : ρ ≤ μ)
    (v : WithTop ℝ≥0)
    (hv : 0 < μ (Ici v)) :
    (∀ t, stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCauseSpecificHazard μ ρ r) id t v ≠ ∞) ∧
      Monotone (fun t ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id t v) ∧
      IsCadlagPath (fun t ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCauseSpecificHazard μ ρ r).toReal) id t v) := by
  cases v using WithTop.recTopCoe with
  | top =>
    simp only [stoppedProcess, id_eq, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe]
    have hsurv (T : ℝ≥0) : 0 < μ (Ici (T : WithTop ℝ≥0)) :=
      hv.trans_le (measure_mono (Ici_subset_Ici.mpr le_top))
    have hfin (t : ℝ≥0) : eCauseSpecificHazard μ ρ t ≠ ∞ :=
      eCauseSpecificHazard_ne_top_of_le μ ρ hρ (hsurv t) le_rfl
    have hm : Monotone (fun t ↦ (eCauseSpecificHazard μ ρ t).toReal) := by
      intro s t hst
      exact (ENNReal.toReal_le_toReal (hfin s) (hfin t)).mpr
        (monotone_eCauseSpecificHazard μ ρ hst)
    refine ⟨hfin, hm, ?_, fun t _ ↦ ⟨_, hm.tendsto_leftLim t⟩⟩
    intro t
    have ht : t < t + 1 := lt_add_of_pos_right t zero_lt_one
    have hc := isRightContinuousPath_eCauseSpecificHazard_toReal_min μ ρ hρ
      (t + 1) (hsurv (t + 1)) t
    change Tendsto (fun r ↦ (eCauseSpecificHazard μ ρ (min r (t + 1))).toReal)
      (𝓝[≥] t) (𝓝 ((eCauseSpecificHazard μ ρ (min t (t + 1))).toReal)) at hc
    rw [min_eq_left ht.le] at hc
    apply hc.congr'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with r hr
    rw [min_eq_left (show r ≤ t + 1 from hr.le)]
  | coe u =>
    simp only [stoppedProcess, id_eq, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe]
    have hfin (t : ℝ≥0) : eCauseSpecificHazard μ ρ (min t u) ≠ ∞ :=
      eCauseSpecificHazard_ne_top_of_le μ ρ hρ hv (min_le_right t u)
    have hm : Monotone (fun t ↦ (eCauseSpecificHazard μ ρ (min t u)).toReal) := by
      intro s t hst
      exact (ENNReal.toReal_le_toReal (hfin s) (hfin t)).mpr
        (monotone_eCauseSpecificHazard μ ρ (min_le_min_right u hst))
    exact ⟨hfin, hm, isRightContinuousPath_eCauseSpecificHazard_toReal_min μ ρ hρ u hv,
      fun t _ ↦ ⟨_, hm.tendsto_leftLim t⟩⟩


/-- One observation-law event gives all-time finiteness, monotonicity and
cadlag regularity of the original stopped cause hazard. -/
theorem ae_stopped_eCauseSpecificHazard_paths (hρ : ρ ≤ μ) :
    ∀ᵐ v ∂μ,
      (∀ t, stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦
        eCauseSpecificHazard μ ρ r) id t v ≠ ∞) ∧
      Monotone (fun t ↦ stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦
        (eCauseSpecificHazard μ ρ r).toReal) id t v) ∧
      IsCadlagPath (fun t ↦ stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦
        (eCauseSpecificHazard μ ρ r).toReal) id t v) := by
  filter_upwards [ae_pos_measure_Ici μ] with v hv
  exact stopped_eCauseSpecificHazard_paths_of_positive_survival μ ρ hρ v hv

end ProbabilityTheory
