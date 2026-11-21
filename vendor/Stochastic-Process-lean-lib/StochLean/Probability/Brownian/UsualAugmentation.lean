/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.IndependentIncrementsAugmentation
public import StochLean.Probability.Brownian.FiltrationMartingale
public import StochLean.Probability.Brownian.SemimartingaleCovariation
public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale

/-! # Brownian motion in a genuinely usual augmented filtration

Finite-dimensional laws and common-event continuity survive measure completion.
Null-set enlargement and right continuation preserve the independent-future
condition. The actual process is therefore a martingale, continuous local
martingale and semimartingale in the augmented filtration; its sole raw bracket
is time. A natural-filtration entry point derives the past independence.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem IsPreBrownianReal.completion (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t (ω : NullMeasurableSpace Ω P) ↦ B t ω) P.completion := by
  exact ⟨fun I ↦ (hB.hasLaw I).completion⟩

theorem IsBrownianReal.completion (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t (ω : NullMeasurableSpace Ω P) ↦ B t ω) P.completion :=
  ⟨hB.toIsPreBrownianReal.completion, hB.cont⟩

theorem IsPreBrownianReal.indep_increment_natural (hB : IsPreBrownianReal B P)
    (hBm : ∀ u, Measurable (B u)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable) s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P := by
  have hi := (hB.indepFun_shift s).comp (measurable_pi_apply (t - s)) measurable_id
  rw [Filtration.natural_eq_comap]
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using
    ((IndepFun_iff_Indep _ _ _).mp hi).symm

variable [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}

theorem IsBrownianReal.martingale_usualAugmentation (hB : IsBrownianReal B P)
    (ha : Adapted F B)
    (hi : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    Martingale (fun t (ω : NullMeasurableSpace Ω P) ↦ B t ω)
      (F.usualAugmentation P) P.completion :=
  hB.completion.toIsPreBrownianReal.martingale_of_indep_past (ha.usualAugmentation P)
    (fun _ _ hst ↦ HasRightContinuousPaths.indep_increment_usualAugmentation
      (hB.cont.mono fun _ hc _ ↦ hc.continuousWithinAt) ha hi hst)

theorem IsBrownianReal.square_sub_time_martingale_usualAugmentation (hB : IsBrownianReal B P)
    (ha : Adapted F B)
    (hi : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    Martingale (fun t (ω : NullMeasurableSpace Ω P) ↦ B t ω ^ 2 - (t : ℝ))
      (F.usualAugmentation P) P.completion :=
  hB.completion.toIsPreBrownianReal.square_sub_time_martingale_of_indep_past
    (ha.usualAugmentation P)
    (fun _ _ hst ↦ HasRightContinuousPaths.indep_increment_usualAugmentation
      (hB.cont.mono fun _ hc _ ↦ hc.continuousWithinAt) ha hi hst)

theorem IsBrownianReal.isContinuousLocalMartingale_usualAugmentation (hB : IsBrownianReal B P)
    (ha : Adapted F B)
    (hi : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    IsContinuousLocalMartingale (fun t (ω : NullMeasurableSpace Ω P) ↦ B t ω)
      (F.usualAugmentation P) P.completion :=
  (hB.martingale_usualAugmentation ha hi).isContinuousLocalMartingale hB.cont

theorem IsBrownianReal.isSemimartingale_usualAugmentation (hB : IsBrownianReal B P)
    (ha : Adapted F B)
    (hi : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    IsSemimartingale (fun t (ω : NullMeasurableSpace Ω P) ↦ B t ω)
      (F.usualAugmentation P) P.completion :=
  (hB.isContinuousLocalMartingale_usualAugmentation ha hi).isSemimartingale
    (F.usualAugmentation_isUsual P)

theorem IsBrownianReal.quadraticVariation_usualAugmentation (hB : IsBrownianReal B P)
    (ha : Adapted F B)
    (hi : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) :
    Indistinguishable ((hB.isSemimartingale_usualAugmentation ha hi).quadraticVariation
      (F.usualAugmentation_isUsual P)) (fun t _ ↦ (t : ℝ)) P.completion :=
  hB.completion.quadraticVariation_eq_time_of_semimartingale
    (hB.isSemimartingale_usualAugmentation ha hi) (F.usualAugmentation_isUsual P)

theorem IsBrownianReal.isContinuousLocalMartingale_natural_usualAugmentation
    (hB : IsBrownianReal B P) (hBm : ∀ u, Measurable (B u)) :
    IsContinuousLocalMartingale (fun t (ω : NullMeasurableSpace Ω P) ↦ B t ω)
      ((Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable)).usualAugmentation P)
      P.completion :=
  hB.isContinuousLocalMartingale_usualAugmentation
    (Filtration.stronglyAdapted_natural _).adapted
    (fun _ _ hst ↦ hB.toIsPreBrownianReal.indep_increment_natural hBm hst)

end ProbabilityTheory
