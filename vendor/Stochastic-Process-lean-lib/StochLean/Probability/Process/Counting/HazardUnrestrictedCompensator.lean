/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardCompensator
public import StochLean.Probability.Process.Counting.HazardPathRegularity
public import StochLean.Probability.Process.Counting.HazardUnrestrictedMartingale
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping

/-! # The unrestricted actual single-jump compensator

The original closed real count is an adapted cadlag process with globally
integrable variation on the genuinely completed lifetime space. Its initial
atom is allowed and remains in the martingale remainder.

The actual stopped hazard is predictable as the pointwise eventually exact
limit of its integer-capped processes: at each finite time every sufficiently
large cap is already equal to the original value. This is not an inference
from separate almost-sure coordinate identities. The previously proved
common-event finite, monotone, cadlag hazard paths supply finite variation.

The actual unrestricted compensated count is a true martingale. The existing
deterministic localization theorem turns that cadlag martingale into a local
martingale, without assuming or inferring uniform integrability on the whole
half-line. Canonical compensator uniqueness then identifies the original
stopped hazard. No deterministic survival guard or support-endpoint exclusion
is imposed, and no alternative compensator or real-hazard selector is defined.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

private theorem isStronglyPredictable_stopped_hazard_unrestricted
    (μ : Measure (WithTop ℝ≥0)) :
    IsStronglyPredictable
      (Filtration.natural
        (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount measurable_id))
      (stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id) := by
  let ℱ := Filtration.natural
    (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount measurable_id)
  let A := stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id
  let : MeasurableSpace (ℝ≥0 × WithTop ℝ≥0) := ℱ.predictable
  change StronglyMeasurable (Function.uncurry A)
  apply stronglyMeasurable_of_tendsto atTop
    (fun n : ℕ ↦ isStronglyPredictable_capped_stopped_eCumulativeHazard μ n)
  apply tendsto_pi_nhds.mpr
  rintro ⟨t, v⟩
  obtain ⟨n, hn⟩ := exists_nat_ge t
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  change A t v = A (min t (m : ℝ≥0)) v
  rw [min_eq_left (hn.trans (Nat.cast_le.mpr hm))]

variable (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ]

/-- The original uncapped real closed count has the actual adapted cadlag
global-IV domain in the genuine usual augmentation. Its initial count may
be nonzero, and its lifetime may be infinite. -/
theorem singleJumpCount_compensator_domain :
    let ℱ := Filtration.natural
      (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount measurable_id)
    let C := fun (t : ℝ≥0) (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦
      (fun w : WithTop ℝ≥0 ↦ if w ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) v
    Adapted (ℱ.usualAugmentation μ) C ∧ HasCadlagPaths C μ.completion ∧
      HasIntegrableVariation C μ.completion := by
  classical
  let ℱ := Filtration.natural
    (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount measurable_id)
  let C := fun (t : ℝ≥0) (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦
    (fun w : WithTop ℝ≥0 ↦ if w ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) v
  let R : NullMeasurableSpace (WithTop ℝ≥0) μ → WithTop ℝ≥0 :=
    (id : WithTop ℝ≥0 → WithTop ℝ≥0)
  have heC : C = fun (t : ℝ≥0) ↦ {v | R v ≤ (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ)) := by
    funext t v
    simp only [C, R, id, indicator_apply, mem_ofPred_eq]
    split_ifs <;> rfl
  have ha : Adapted (ℱ.usualAugmentation μ) C := by
    intro t
    convert (capped_singleJumpCount_compensator_domain μ t).1 t using 1
    funext v
    simp only [C, min_self]
    split_ifs <;> rfl
  have hc : HasCadlagPaths C μ.completion := by
    rw [heC]
    exact Eventually.of_forall fun v ↦ isCadlagPath_indicator_lifetime_le R (fun _ ↦ 1) v
  have hiR : Measurable R := by
    exact (show @Measurable (NullMeasurableSpace (WithTop ℝ≥0) μ) (WithTop ℝ≥0)
      inferInstance WithTop.instMeasurableSpace (id : WithTop ℝ≥0 → WithTop ℝ≥0) from
        fun _ hs ↦ hs.nullMeasurableSet (μ := μ))
  have hv : HasIntegrableVariation C μ.completion := by
    rw [heC]
    exact hasIntegrableVariation_indicator_lifetime_le hiR (integrable_const (1 : ℝ))
  exact ⟨ha, hc, hv⟩

/-- Without any horizon or survival guard, the actual sole compensator of
the original closed count is its original stopped cumulative hazard. The
completion, process-domain evidence and local-martingale remainder are all
constructed from the lifetime probability law. -/
theorem predictableCompensator_singleJumpCount_eq_stopped_hazard :
    let ℱ := Filtration.natural
      (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount measurable_id)
    let hD := singleJumpCount_compensator_domain μ
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (ℱ.usualAugmentation_isUsual μ) hD.2.1)
      (fun t (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v)
      μ.completion := by
  classical
  let ℱ := Filtration.natural
    (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount measurable_id)
  let F := ℱ.usualAugmentation μ
  let C := fun (t : ℝ≥0) (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦
    (fun w : WithTop ℝ≥0 ↦ if w ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) v
  let A := fun t (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦ stoppedProcess
    (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id t v
  have hD := singleJumpCount_compensator_domain μ
  have hF : F.IsUsual μ.completion := ℱ.usualAugmentation_isUsual μ
  have hpred : ℱ.predictable ≤ F.predictable := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro E hE
      exact measurableSet_predictable_singleton_bot_prod (ℱ.le_usualAugmentation μ 0 E hE)
    · intro t E hE
      exact measurableSet_predictable_Ioi_prod (ℱ.le_usualAugmentation μ t E hE)
  have hpA : IsStronglyPredictable F A :=
    (isStronglyPredictable_stopped_hazard_unrestricted μ).mono hpred
  have hcA : HasCadlagPaths A μ.completion := hasCadlagPaths_stopped_eCumulativeHazard μ
  have hmA : HasMonotonePaths A μ.completion := hasMonotonePaths_stopped_eCumulativeHazard μ
  have hA0 : A 0 =ᵐ[μ.completion] 0 := Eventually.of_forall fun v ↦ by
    change (eCumulativeHazard μ (min ((0 : ℝ≥0) : WithTop ℝ≥0) v).untopA).toReal = 0
    rw [min_eq_left (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ v from bot_le)]
    change (eCumulativeHazard μ 0).toReal = 0
    rw [eCumulativeHazard_zero, ENNReal.toReal_zero]
  have hM : Martingale (C - A) F μ.completion :=
    (martingale_singleJump_sub_hazard_unrestricted μ).usualAugmentation_of_isRightContinuous
      (natural_singleJumpCount_isRightContinuous measurable_id)
  exact hD.2.2.hasLocallyIntegrableVariation.predictableCompensator_unique hD.1 hF hD.2.1
    hpA hmA.hasFiniteVariationPaths hA0 (hM.isLocalMartingale (hD.2.1.sub hcA))

end ProbabilityTheory
