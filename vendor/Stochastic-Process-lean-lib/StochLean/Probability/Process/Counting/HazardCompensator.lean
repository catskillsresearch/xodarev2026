/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardMartingale
public import StochLean.Probability.Process.Counting.HazardPredictable
public import StochLean.Probability.Process.Counting.SingleJumpRightContinuous
public import StochLean.Probability.Process.Filtration.MartingaleAugmentation
public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.FiniteVariation.SingleJump
public import StochLean.Probability.Martingale.MonotonePaths
public import StochLean.Probability.Process.Path.Subtraction

/-! # The actual finite-horizon single-jump compensator

The capped closed count has actual globally integrable variation: it is the
closed unit step at the original lifetime restricted to occurrence by the
cap. Adaptedness and cadlag paths are also constructed, without requiring
an initial zero count or supplying a compensator-domain certificate.

In the genuinely completed probability space, the usual augmentation of
the original full-count natural filtration preserves the actual UI
martingale proved in `HazardMartingale`. The actual stopped hazard is
predictable, cadlag, of finite variation and initially zero. Uniqueness of
the sole canonical compensator therefore identifies it with this hazard.

Positive pre-jump survival at the finite cap is used to prove extended
finiteness before comparing real hazards. The count may have an atom at
zero; that initial count remains in the martingale remainder. Infinite
lifetimes and the closed observation endpoint are retained exactly.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

private theorem capped_count_eq_restricted_step (T : ℝ≥0) :
    (fun t (v : WithTop ℝ≥0) ↦
      if v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) =
      fun (t : ℝ≥0) ↦ {v | restrictedStoppingTime id {v | v ≤ (T : WithTop ℝ≥0)} v ≤
        (t : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext t v
  by_cases hv : v ≤ (T : WithTop ℝ≥0)
  · have hR : restrictedStoppingTime id {v | v ≤ (T : WithTop ℝ≥0)} v = v :=
      restrictedStoppingTime_of_mem id hv
    have he : v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) ↔ v ≤ (t : WithTop ℝ≥0) := by
      rw [WithTop.coe_min, le_min_iff]
      exact and_iff_left hv
    simp only [indicator_apply, mem_ofPred_eq, hR, he]
  · have hR : restrictedStoppingTime id {v | v ≤ (T : WithTop ℝ≥0)} v = ⊤ :=
      restrictedStoppingTime_of_notMem id hv
    have he : ¬v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) :=
      fun h ↦ hv (h.trans (WithTop.coe_le_coe.mpr (min_le_right t T)))
    simp only [indicator_apply, mem_ofPred_eq, hR, WithTop.not_top_le_coe, if_false, he]

variable (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ]

/-- The capped real closed count has the actual adapted cadlag global-IV
domain on the completed space, even when the original lifetime has an
initial atom. No survival condition is needed for this source domain. -/
theorem capped_singleJumpCount_compensator_domain (T : ℝ≥0) :
    let ℱ := Filtration.natural
      (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount measurable_id)
    let C := fun t (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦
      (fun w : WithTop ℝ≥0 ↦
        if w ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) v
    Adapted (ℱ.usualAugmentation μ) C ∧ HasCadlagPaths C μ.completion ∧
      HasIntegrableVariation C μ.completion := by
  classical
  let N : ℝ≥0 → WithTop ℝ≥0 → ℕ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount measurable_id)
  let C := fun t (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦
    (fun w : WithTop ℝ≥0 ↦
      if w ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) v
  let R : NullMeasurableSpace (WithTop ℝ≥0) μ → WithTop ℝ≥0 :=
    restrictedStoppingTime (id : WithTop ℝ≥0 → WithTop ℝ≥0)
      {v : WithTop ℝ≥0 | v ≤ (T : WithTop ℝ≥0)}
  have heC : C = fun (t : ℝ≥0) ↦ {v | R v ≤ (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ)) := capped_count_eq_restricted_step T
  have hN : StronglyAdapted ℱ N :=
    Filtration.stronglyAdapted_natural (stronglyMeasurable_singleJumpCount measurable_id)
  have ha : Adapted (ℱ.usualAugmentation μ) C := by
    intro t
    have he : {v : WithTop ℝ≥0 | v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0)} =
        N (min t T) ⁻¹' {1} := by
      ext v
      change v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) ↔
        (if v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℕ) else 0) = 1
      by_cases h : v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0)
      · rw [if_pos h]
        exact iff_of_true h rfl
      · rw [if_neg h]
        exact iff_of_false h Nat.zero_ne_one
    have hs : MeasurableSet[ℱ t]
        {v : WithTop ℝ≥0 | v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0)} := by
      rw [he]
      exact (hN.stronglyMeasurable_le (min_le_left t T)).measurable
        (measurableSet_singleton 1)
    have hm : Measurable[ℱ t] (fun v : WithTop ℝ≥0 ↦
        if v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
      Measurable.ite hs measurable_const measurable_const
    exact hm.mono (ℱ.le_usualAugmentation μ t) le_rfl
  have hc : HasCadlagPaths C μ.completion := by
    rw [heC]
    exact Eventually.of_forall fun v ↦ isCadlagPath_indicator_lifetime_le R (fun _ ↦ 1) v
  have hiR : Measurable R := by
    have hi : @Measurable (NullMeasurableSpace (WithTop ℝ≥0) μ) (WithTop ℝ≥0)
        inferInstance WithTop.instMeasurableSpace (id : WithTop ℝ≥0 → WithTop ℝ≥0) :=
      fun _ hs ↦ hs.nullMeasurableSet (μ := μ)
    exact Measurable.ite (measurableSet_le hi measurable_const) hi measurable_const
  have hv : HasIntegrableVariation C μ.completion := by
    rw [heC]
    exact hasIntegrableVariation_indicator_lifetime_le hiR (integrable_const (1 : ℝ))
  exact ⟨ha, hc, hv⟩

/-- The sole canonical compensator of the actual capped closed count is
its actual stopped cumulative hazard in the genuine usual augmentation.
The source-domain evidence is constructed by the preceding theorem. -/
theorem predictableCompensator_capped_singleJumpCount_eq_stopped_hazard
    (T : ℝ≥0) (hT : 0 < μ (Ici (T : WithTop ℝ≥0))) :
    let ℱ := Filtration.natural
      (fun (s : ℝ≥0) (v : WithTop ℝ≥0) ↦ if v ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount measurable_id)
    let hD := capped_singleJumpCount_compensator_domain μ T
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (ℱ.usualAugmentation_isUsual μ) hD.2.1)
      (fun t (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id (min t T) v)
      μ.completion := by
  classical
  let N : ℝ≥0 → WithTop ℝ≥0 → ℕ := fun s v ↦ if v ≤ (s : WithTop ℝ≥0) then 1 else 0
  let ℱ := Filtration.natural N (stronglyMeasurable_singleJumpCount measurable_id)
  let F := ℱ.usualAugmentation μ
  let C := fun t (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦
    (fun w : WithTop ℝ≥0 ↦
      if w ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) v
  let A := fun t (v : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦ stoppedProcess
    (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal) id (min t T) v
  let b : ℝ≥0 → ℝ := fun t ↦ (eCumulativeHazard μ (min t T)).toReal
  have hD := capped_singleJumpCount_compensator_domain μ T
  have hF : F.IsUsual μ.completion := ℱ.usualAugmentation_isUsual μ
  have hpred : ℱ.predictable ≤ F.predictable := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro E hE
      exact measurableSet_predictable_singleton_bot_prod (ℱ.le_usualAugmentation μ 0 E hE)
    · intro t E hE
      exact measurableSet_predictable_Ioi_prod (ℱ.le_usualAugmentation μ t E hE)
  have hpA : IsStronglyPredictable F A :=
    (isStronglyPredictable_capped_stopped_eCumulativeHazard μ T).mono hpred
  have hbf (t : ℝ≥0) : eCumulativeHazard μ (min t T) ≠ ∞ :=
    eCumulativeHazard_ne_top_of_le μ hT (min_le_right t T)
  have hbm : Monotone b := by
    intro s t hst
    exact (ENNReal.toReal_le_toReal (hbf s) (hbf t)).mpr
      (monotone_eCumulativeHazard μ (min_le_min_right T hst))
  have hbc : IsCadlagPath b :=
    ⟨isRightContinuousPath_eCumulativeHazard_toReal_min μ T hT,
      fun t _ ↦ ⟨Function.leftLim b t, hbm.tendsto_leftLim t⟩⟩
  have heA : A = stoppedProcess
      (fun t (_ : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦ b t) id := by
    funext t v
    change (eCumulativeHazard μ
      (min ((min t T : ℝ≥0) : WithTop ℝ≥0) v).untopA).toReal =
        (eCumulativeHazard μ (min (min (t : WithTop ℝ≥0) v).untopA T)).toReal
    cases v using WithTop.recTopCoe with
    | top =>
        simp only [min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
    | coe u =>
        simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
        rw [min_right_comm]
  have hcA : HasCadlagPaths A μ.completion := by
    rw [heA]
    have hcb : HasCadlagPaths
        (fun t (_ : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦ b t) μ.completion :=
      Eventually.of_forall fun _ ↦ hbc
    exact hcb.stoppedProcess id
  have hmA : HasMonotonePaths A μ.completion := by
    rw [heA]
    have hmb : HasMonotonePaths
        (fun t (_ : NullMeasurableSpace (WithTop ℝ≥0) μ) ↦ b t) μ.completion :=
      Eventually.of_forall fun _ ↦ hbm
    exact hmb.stoppedProcess id
  have hA0 : A 0 =ᵐ[μ.completion] 0 := Eventually.of_forall fun v ↦ by
    change (eCumulativeHazard μ
      (min ((min (0 : ℝ≥0) T : ℝ≥0) : WithTop ℝ≥0) v).untopA).toReal = 0
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le),
      min_eq_left (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ v from bot_le)]
    change (eCumulativeHazard μ 0).toReal = 0
    rw [eCumulativeHazard_zero, ENNReal.toReal_zero]
  have huRaw : IsUIMartingale
      (fun t (v : WithTop ℝ≥0) ↦
        (if v ≤ ((min t T : ℝ≥0) : WithTop ℝ≥0) then (1 : ℝ) else 0) -
        stoppedProcess (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard μ r).toReal)
          id (min t T) v) ℱ μ :=
    ⟨martingale_capped_singleJump_sub_hazard μ T hT,
      uniformIntegrable_capped_singleJump_sub_hazard μ T hT⟩
  have hu : IsUIMartingale (C - A) F μ.completion :=
    huRaw.usualAugmentation_of_isRightContinuous
      (natural_singleJumpCount_isRightContinuous measurable_id)
  exact hD.2.2.hasLocallyIntegrableVariation.predictableCompensator_unique hD.1 hF hD.2.1
    hpA hmA.hasFiniteVariationPaths hA0 (hu.isLocalMartingale (hD.2.1.sub hcA))

end ProbabilityTheory
