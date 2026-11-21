/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Hazard
public import StochLean.ForMathlib.MeasureTheory.OrderSurvival
public import StochLean.Probability.Process.Path.Cadlag
public import StochLean.Probability.Process.Path.FiniteVariation
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Order.LeftRightLim

/-! # Almost-sure path regularity of the actual uncapped stopped hazard

Almost every lifetime has strictly positive closed survival mass at its own
value. On this one common event, every finite observation clock stopped at
the lifetime has finite extended hazard, before any conversion to real values.

At a finite lifetime, the original stopped hazard is the existing deterministic
hazard capped at that lifetime. At an infinite lifetime with positive mass,
every finite cap has positive survival; a cap just beyond each observation
time proves right continuity locally. Monotonicity supplies the finite left
limits and, through the existing path theorem, compact finite variation.

No pointwise regularity is claimed at null support endpoints, no positive
survival condition at a fixed deterministic horizon is assumed, and no
replacement hazard process is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (μ : Measure (WithTop ℝ≥0)) [IsFiniteMeasure μ]

/-- Positive closed survival at an actual lifetime gives all finite stopped
hazard values and the monotone cadlag path together, with no version change.
The pointwise guard makes the same proof reusable for measurable lifetime kernels. -/
theorem stopped_eCumulativeHazard_paths_of_positive_survival (v : WithTop ℝ≥0)
    (hv : 0 < μ (Ici v)) :
    (∀ t, stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v ≠ ∞) ∧
      Monotone (fun t ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v) ∧
      IsCadlagPath (fun t ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v) := by
  cases v using WithTop.recTopCoe with
  | top =>
    simp only [stoppedProcess, id_eq, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe]
    have hsurv (T : ℝ≥0) : 0 < μ (Ici (T : WithTop ℝ≥0)) :=
      hv.trans_le (measure_mono (Ici_subset_Ici.mpr le_top))
    have hfin (t : ℝ≥0) : eCumulativeHazard μ t ≠ ∞ :=
      eCumulativeHazard_ne_top_of_le μ (hsurv t) le_rfl
    have hm : Monotone (fun t ↦ (eCumulativeHazard μ t).toReal) := by
      intro s t hst
      exact (ENNReal.toReal_le_toReal (hfin s) (hfin t)).mpr
        (monotone_eCumulativeHazard μ hst)
    refine ⟨hfin, hm, ?_, fun t _ ↦ ⟨_, hm.tendsto_leftLim t⟩⟩
    intro t
    have ht : t < t + 1 := lt_add_of_pos_right t zero_lt_one
    have hc := isRightContinuousPath_eCumulativeHazard_toReal_min μ
      (t + 1) (hsurv (t + 1)) t
    change Tendsto (fun r ↦ (eCumulativeHazard μ (min r (t + 1))).toReal)
      (𝓝[≥] t) (𝓝 ((eCumulativeHazard μ (min t (t + 1))).toReal)) at hc
    rw [min_eq_left ht.le] at hc
    apply hc.congr'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with r hr
    rw [min_eq_left (show r ≤ t + 1 from hr.le)]
  | coe u =>
    simp only [stoppedProcess, id_eq, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe]
    have hfin (t : ℝ≥0) : eCumulativeHazard μ (min t u) ≠ ∞ :=
      eCumulativeHazard_ne_top_of_le μ hv (min_le_right t u)
    have hm : Monotone (fun t ↦ (eCumulativeHazard μ (min t u)).toReal) := by
      intro s t hst
      exact (ENNReal.toReal_le_toReal (hfin s) (hfin t)).mpr
        (monotone_eCumulativeHazard μ (min_le_min_right u hst))
    exact ⟨hfin, hm, isRightContinuousPath_eCumulativeHazard_toReal_min μ u hv,
      fun t _ ↦ ⟨_, hm.tendsto_leftLim t⟩⟩

/-- On a common event all finite observation times have genuinely finite
extended stopped hazard, without a deterministic survival guard. -/
theorem ae_forall_stoppedProcess_eCumulativeHazard_ne_top :
    ∀ᵐ v ∂μ, ∀ t, stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard μ r) id t v ≠ ∞ := by
  filter_upwards [ae_pos_measure_Ici μ] with v hv
  exact (stopped_eCumulativeHazard_paths_of_positive_survival μ v hv).1

/-- The original real stopped hazard has monotone paths on one common
event. The existing monotone-path theorem then gives compact finite variation. -/
theorem hasMonotonePaths_stopped_eCumulativeHazard :
    HasMonotonePaths (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id) μ := by
  filter_upwards [ae_pos_measure_Ici μ] with v hv
  exact (stopped_eCumulativeHazard_paths_of_positive_survival μ v hv).2.1

/-- The actual uncapped stopped hazard is cadlag almost surely, including
finite terminal atoms and infinite lifetimes with positive mass. -/
theorem hasCadlagPaths_stopped_eCumulativeHazard :
    HasCadlagPaths (stoppedProcess
      (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id) μ := by
  filter_upwards [ae_pos_measure_Ici μ] with v hv
  exact (stopped_eCumulativeHazard_paths_of_positive_survival μ v hv).2.2

end ProbabilityTheory
