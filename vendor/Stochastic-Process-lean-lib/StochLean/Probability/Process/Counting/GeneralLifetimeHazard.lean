/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardUnrestrictedCompensator
public import StochLean.Probability.Process.Filtration.MartingalePullback

/-! # The actual hazard compensator of an arbitrary measurable lifetime

The original lifetime may live on any probability space. Its actual law is
the pushforward measure, and the canonical lifetime-space martingale pulls
back to the exact natural filtration of the original closed Nat-valued count.
The genuinely usual augmentation preserves that actual martingale.

The original stopped hazard is predictable by stopping its deterministic
Borel time path at the original stopping time. Its common-event cadlag and
monotone paths pull back from the actual lifetime law. The count's actual
global integrable variation and full compensator uniqueness then identify
the sole selected compensator, not a newly chosen process.

Zero and infinite lifetimes, finite terminal atoms and zero-survival support
endpoints are retained. No initial-zero, finite-lifetime or deterministic
positive-survival hypothesis is required. This is only the general-lifetime
compensator formula: CDF/logarithm, absolute-continuity and exponential-law
specializations are not asserted here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0}

/-- The original closed count minus the hazard of its actual lifetime law
is a true martingale in its own raw natural filtration. -/
theorem martingale_singleJump_sub_hazard_map (hτ : Measurable τ) :
    Martingale (fun (t : ℝ≥0) ω ↦
      (if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ t ω)
      (Filtration.natural
        (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount hτ)) P := by
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  exact Martingale.comp_measurePreserving (hτ.measurePreserving P)
    (martingale_singleJump_sub_hazard_unrestricted (P.map τ))
    (fun t ↦ Filtration.natural_comp_eq_comap hτ
      (stronglyMeasurable_singleJumpCount measurable_id) t)

private theorem stronglyMeasurable_real_singleJumpCount_natural
    (hτ : Measurable τ) (t : ℝ≥0) :
    StronglyMeasurable[(Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)) t]
      (fun ω ↦ if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) := by
  classical
  let N : ℝ≥0 → Ω → ℕ := fun s ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then 1 else 0
  let F := Filtration.natural N (stronglyMeasurable_singleJumpCount hτ)
  have hN : StronglyAdapted F N :=
    Filtration.stronglyAdapted_natural (stronglyMeasurable_singleJumpCount hτ)
  have he : {ω | τ ω ≤ (t : WithTop ℝ≥0)} = N t ⁻¹' {1} := by
    ext ω
    change τ ω ≤ (t : WithTop ℝ≥0) ↔
      (if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℕ) else 0) = 1
    by_cases h : τ ω ≤ (t : WithTop ℝ≥0)
    · exact iff_of_true h (if_pos h)
    · rw [if_neg h]
      exact iff_of_false h Nat.zero_ne_one
  have hs : MeasurableSet[F t] {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
    rw [he]
    exact (hN t).measurable (measurableSet_singleton 1)
  exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable

omit [IsProbabilityMeasure P] in
private theorem isStronglyPredictable_stopped_hazard_map (hτ : Measurable τ) :
    IsStronglyPredictable
      (Filtration.natural
        (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount hτ))
      (stoppedProcess (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ) := by
  classical
  let F := Filtration.natural
    (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount hτ)
  have hstop : IsStoppingTime F τ := by
    intro s
    have he : {ω | τ ω ≤ (s : WithTop ℝ≥0)} =
        (fun ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℝ) else 0) ⁻¹' {1} := by
      ext ω
      change τ ω ≤ (s : WithTop ℝ≥0) ↔
        (if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℝ) else 0) = 1
      by_cases h : τ ω ≤ (s : WithTop ℝ≥0)
      · exact iff_of_true h (if_pos h)
      · rw [if_neg h]
        exact iff_of_false h zero_ne_one
    rw [he]
    exact (stronglyMeasurable_real_singleJumpCount_natural hτ s).measurable
      (measurableSet_singleton 1)
  have htime : Measurable[F.predictable] (Prod.fst : ℝ≥0 × Ω → ℝ≥0) := by
    apply measurable_of_Ioi
    intro s
    simpa only [prod_univ] using
      measurableSet_predictable_Ioi_prod (𝓕 := F) (i := s) MeasurableSet.univ
  have hdet : IsStronglyPredictable F
      (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) :=
    ((measurable_eCumulativeHazard (P.map τ)).ennreal_toReal.comp htime).stronglyMeasurable
  exact hdet.stoppedProcess hstop

/-- On the genuinely completed original sample space, the original count
has an actual adapted cadlag global-integrable-variation compensator domain. -/
theorem singleJumpCount_compensator_domain_map (hτ : Measurable τ) :
    let F := Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)
    let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
      if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0
    Adapted (F.usualAugmentation P) C ∧ HasCadlagPaths C P.completion ∧
      HasIntegrableVariation C P.completion := by
  classical
  let F := Filtration.natural
    (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount hτ)
  let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0
  let R : NullMeasurableSpace Ω P → WithTop ℝ≥0 := fun ω ↦ τ ω
  have heC : C = fun t : ℝ≥0 ↦ {ω | R ω ≤ (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ)) := by
    funext t ω
    simp only [C, R, indicator_apply, mem_ofPred_eq]
  have ha : Adapted (F.usualAugmentation P) C := fun t ↦
    (stronglyMeasurable_real_singleJumpCount_natural hτ t).measurable.mono
      (F.le_usualAugmentation P t) le_rfl
  have hc : HasCadlagPaths C P.completion := by
    rw [heC]
    exact ae_of_all _ fun ω ↦ isCadlagPath_indicator_lifetime_le R (fun _ ↦ 1) ω
  have hmR : Measurable R := fun B hB ↦ (hτ hB).nullMeasurableSet (μ := P)
  have hv : HasIntegrableVariation C P.completion := by
    rw [heC]
    exact hasIntegrableVariation_indicator_lifetime_le hmR (integrable_const (1 : ℝ))
  exact ⟨ha, hc, hv⟩

/-- The actual sole compensator equals the original stopped hazard of the
pushforward lifetime law, in the genuine usual natural filtration. The law,
process domain and martingale remainder are constructed from the measurable
lifetime; no compensator, survival or path certificate is a hypothesis. -/
theorem predictableCompensator_singleJumpCount_eq_stopped_hazard_map (hτ : Measurable τ) :
    let F := Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)
    let hD := singleJumpCount_compensator_domain_map (P := P) hτ
    Indistinguishable
      (hD.2.2.hasLocallyIntegrableVariation.predictableCompensator hD.1
        (F.usualAugmentation_isUsual P) hD.2.1)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ stoppedProcess
        (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ t ω)
      P.completion := by
  classical
  let : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  let F := Filtration.natural
    (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
    (stronglyMeasurable_singleJumpCount hτ)
  let G := F.usualAugmentation P
  let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
    if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0
  let A := fun t (ω : NullMeasurableSpace Ω P) ↦ stoppedProcess
    (fun r (_ : Ω) ↦ (eCumulativeHazard (P.map τ) r).toReal) τ t ω
  have hD := singleJumpCount_compensator_domain_map (P := P) hτ
  have hG : G.IsUsual P.completion := F.usualAugmentation_isUsual P
  have hpred : F.predictable ≤ G.predictable := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro E hE
      exact measurableSet_predictable_singleton_bot_prod (F.le_usualAugmentation P 0 E hE)
    · intro t E hE
      exact measurableSet_predictable_Ioi_prod (F.le_usualAugmentation P t E hE)
  have hpA : IsStronglyPredictable G A :=
    (isStronglyPredictable_stopped_hazard_map (P := P) hτ).mono hpred
  have hcA : HasCadlagPaths A P.completion :=
    ae_of_ae_map (μ := P) hτ.aemeasurable
      (hasCadlagPaths_stopped_eCumulativeHazard (P.map τ))
  have hmA : HasMonotonePaths A P.completion :=
    ae_of_ae_map (μ := P) hτ.aemeasurable
      (hasMonotonePaths_stopped_eCumulativeHazard (P.map τ))
  have hA0 : A 0 =ᵐ[P.completion] 0 := ae_of_all _ fun ω ↦ by
    change (eCumulativeHazard (P.map τ)
      (min ((0 : ℝ≥0) : WithTop ℝ≥0) (τ ω)).untopA).toReal = 0
    rw [min_eq_left (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from bot_le)]
    change (eCumulativeHazard (P.map τ) 0).toReal = 0
    rw [eCumulativeHazard_zero, ENNReal.toReal_zero]
  have hM : Martingale (C - A) G P.completion :=
    (martingale_singleJump_sub_hazard_map (P := P) hτ).usualAugmentation_of_isRightContinuous
      (natural_singleJumpCount_isRightContinuous hτ)
  exact hD.2.2.hasLocallyIntegrableVariation.predictableCompensator_unique hD.1 hG hD.2.1
    hpA hmA.hasFiniteVariationPaths hA0 (hM.isLocalMartingale (hD.2.1.sub hcA))

end ProbabilityTheory
