/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.MarkedSingleJumpHazardMartingale
public import StochLean.Probability.Process.Counting.MarkedSingleJumpRightContinuous
public import StochLean.Probability.Process.Counting.CauseSpecificHazardPaths
public import StochLean.Probability.Process.Counting.GeneralLifetimeHazard

/-! # The actual marked single-jump compensator

The marked arrival count is observed together with its complementary cause.
Its canonical compensator uses the observation lifetime law for survival
and the actual arrival-marked submeasure for integration. The mark is not
revealed before the observation. A true raw-filtration martingale, genuine
right continuity, predictable stopping and actual monotone cadlag hazard
paths supply the full canonical uniqueness argument.

The source process has actual global integrable variation, derived from
its bounded marked lifetime jump. Zero and infinite lifetimes remain
allowed. No candidate compensator, path regularity or moment certificate
is an input, and no new compensator selector is defined.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0} {B : Set Ω}

open Classical in
/-- The original marked count has the true canonical compensation domain
in the genuine usual natural filtration of both observed causes. -/
theorem markedSingleJumpCount_compensator_domain (hτ : Measurable τ) (hB : MeasurableSet B) :
    let F := Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)
    let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
      if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℝ) else 0
    Adapted (F.usualAugmentation P) C ∧ HasCadlagPaths C P.completion ∧
      HasIntegrableVariation C P.completion := by
  let X : ℝ≥0 → Ω → ℕ × ℕ := fun t ω ↦
    (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then 1 else 0,
     if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then 1 else 0)
  let F := Filtration.natural X (stronglyMeasurable_markedSingleJumpCount hτ hB)
  let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℝ) else 0
  let R : NullMeasurableSpace Ω P → WithTop ℝ≥0 := fun ω ↦ τ ω
  let Z : NullMeasurableSpace Ω P → ℝ := B.indicator (fun _ ↦ 1)
  have haX := Filtration.stronglyAdapted_natural
    (stronglyMeasurable_markedSingleJumpCount hτ hB)
  have ha : Adapted (F.usualAugmentation P) C := by
    intro t
    have hm : Measurable[F t] (fun ω ↦ ((X t ω).1 : ℝ)) :=
      (measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp (haX t).measurable.fst
    have he : (fun ω ↦ ((X t ω).1 : ℝ)) =
        (fun ω ↦ if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℝ) else 0) := by
      funext ω
      by_cases hω : τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B
      · simp only [X, if_pos hω, Nat.cast_one]
      · simp only [X, if_neg hω, Nat.cast_zero]
    rw [he] at hm
    exact hm.mono (F.le_usualAugmentation P t) le_rfl
  have heC : C = fun t : ℝ≥0 ↦ {ω | R ω ≤ (t : WithTop ℝ≥0)}.indicator Z := by
    have he : (fun (t : ℝ≥0) (ω : Ω) ↦
        if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℝ) else 0) =
        fun t : ℝ≥0 ↦ {ω : Ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
          (B.indicator (fun _ : Ω ↦ (1 : ℝ))) := by
      funext t ω
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      by_cases hω : ω ∈ B <;> simp only [hω, and_true, and_false,
        ite_true, ite_false, ite_self]
    exact he
  have hc : HasCadlagPaths C P.completion := by
    rw [heC]
    exact ae_of_all _ fun ω ↦ isCadlagPath_indicator_lifetime_le R Z ω
  have hR : Measurable R := fun D hD ↦ (hτ hD).nullMeasurableSet (μ := P)
  have hZ : Integrable Z P.completion :=
    (integrable_const (1 : ℝ)).indicator (hB.nullMeasurableSet (μ := P))
  have hv : HasIntegrableVariation C P.completion := by
    rw [heC]
    exact hasIntegrableVariation_indicator_lifetime_le hR hZ
  exact ⟨ha, hc, hv⟩

open Classical in
/-- The sole selected compensator of the observed marked count is the
actual cause-specific hazard stopped at the observation lifetime. -/
theorem predictableCompensator_markedSingleJumpCount_eq_stopped_cause_hazard
    (hτ : Measurable τ) (hB : MeasurableSet B) :
    let F := Filtration.natural
      (fun (t : ℝ≥0) ω ↦
        (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
         if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
      (stronglyMeasurable_markedSingleJumpCount hτ hB)
    let hD := markedSingleJumpCount_compensator_domain (P := P) hτ hB
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ stoppedProcess
        (fun r (_ : Ω) ↦ (eCauseSpecificHazard (P.map τ) ((P.restrict B).map τ) r).toReal)
        τ t ω)
      P.completion := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  let F := Filtration.natural
    (fun (t : ℝ≥0) ω ↦
      (if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℕ) else 0,
       if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∉ B then (1 : ℕ) else 0))
    (stronglyMeasurable_markedSingleJumpCount hτ hB)
  let G := F.usualAugmentation P
  let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    if τ ω ≤ (t : WithTop ℝ≥0) ∧ ω ∈ B then (1 : ℝ) else 0
  let A := fun t (ω : NullMeasurableSpace Ω P) ↦ stoppedProcess
    (fun r (_ : Ω) ↦ (eCauseSpecificHazard (P.map τ) ((P.restrict B).map τ) r).toReal)
    τ t ω
  have hD := markedSingleJumpCount_compensator_domain (P := P) hτ hB
  have hG : G.IsUsual P.completion := F.usualAugmentation_isUsual P
  have hpred : F.predictable ≤ G.predictable := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro E hE
      exact measurableSet_predictable_singleton_bot_prod (F.le_usualAugmentation P 0 E hE)
    · intro t E hE
      exact measurableSet_predictable_Ioi_prod (F.le_usualAugmentation P t E hE)
  have hpA : IsStronglyPredictable G A :=
    (isStronglyPredictable_stopped_causeSpecificHazard_marked (P := P) hτ hB).mono hpred
  have hρ : (P.restrict B).map τ ≤ P.map τ := Measure.map_mono Measure.restrict_le_self hτ
  have hpaths := ae_of_ae_map (μ := P) hτ.aemeasurable
    (ae_stopped_eCauseSpecificHazard_paths (P.map τ) ((P.restrict B).map τ) hρ)
  have hcA : HasCadlagPaths A P.completion := by
    filter_upwards [hpaths] with ω hω
    exact hω.2.2
  have hmA : HasMonotonePaths A P.completion := by
    filter_upwards [hpaths] with ω hω
    exact hω.2.1
  have hA0 : A 0 =ᵐ[P.completion] 0 := ae_of_all _ fun ω ↦ by
    change (eCauseSpecificHazard (P.map τ) ((P.restrict B).map τ)
      (min ((0 : ℝ≥0) : WithTop ℝ≥0) (τ ω)).untopA).toReal = 0
    rw [min_eq_left (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from bot_le)]
    change (eCauseSpecificHazard (P.map τ) ((P.restrict B).map τ) 0).toReal = 0
    rw [eCauseSpecificHazard_zero, ENNReal.toReal_zero]
  have hraw := martingale_markedSingleJump_sub_causeSpecificHazard (P := P) hτ hB
  have hM : Martingale (C - A) G P.completion :=
    hraw.usualAugmentation_of_isRightContinuous
      (natural_markedSingleJumpCount_isRightContinuous hτ hB)
  exact hD.2.2.hasLocallyIntegrableVariation.predictableCompensator_unique hD.1 hG hD.2.1
    hpA hmA.hasFiniteVariationPaths hA0 (hM.isLocalMartingale (hD.2.1.sub hcA))

end ProbabilityTheory
