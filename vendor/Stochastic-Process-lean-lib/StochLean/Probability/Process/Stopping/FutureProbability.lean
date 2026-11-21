/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ConditionalRegularization
public import StochLean.Probability.Process.Stopping.AfterCoefficient
public import StochLean.Probability.Process.Path.RightContinuousOrder

/-! # Cadlag conditional probabilities of an approaching stopping time

For a fixed nonnegative delay, the conditional probability of `τ ≤ t + δ`
has a cadlag submartingale version under usual conditions. On one common
full-measure event it lies between the already-revealed indicator `τ ≤ t`
and one. The input indicator family is not assumed adapted.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

theorem IsStoppingTime.exists_cadlag_conditional_future (hτ : IsStoppingTime F τ)
    (hF : F.IsUsual P) (δ : ℝ≥0) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Submartingale Y F P ∧ HasCadlagPaths Y P ∧
      IsModification
        (fun t ↦ P[{ω | τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) | F t])
        Y P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω ≤ Y t ω ∧
        Y t ω ≤ 1 := by
  classical
  let H : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator (fun _ ↦ 1)
  let C : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ 1)
  have hm (t) : AEStronglyMeasurable (H t) P :=
    (stronglyMeasurable_const.indicator (F.le (t + δ) _ (hτ (t + δ)))).aestronglyMeasurable
  have hb (t) : ∀ᵐ ω ∂P, ‖H t ω‖ ≤ (1 : ℝ) := by
    filter_upwards with ω
    exact (norm_indicator_le_norm_self (fun _ : Ω ↦ (1 : ℝ)) ω).trans_eq (norm_one (α := ℝ))
  have hi (t) : Integrable (H t) P := (integrable_const (1 : ℝ)).mono' (hm t) (hb t)
  have hr : HasRightContinuousPaths H P := by
    filter_upwards with ω
    intro t
    have hc := (isCadlagPath_indicator_lifetime_le τ (fun _ ↦ (1 : ℝ)) ω).1 (t + δ)
    have hadd : ContinuousWithinAt (fun s : ℝ≥0 ↦ s + δ) (Ici t) t :=
      (continuous_id.add continuous_const).continuousWithinAt
    exact hc.comp (f := fun s : ℝ≥0 ↦ s + δ) (x := t) hadd
      (fun s hs ↦ show t + δ ≤ s + δ from add_le_add (show t ≤ s from hs) le_rfl)
  have hmono : ∀ s t, s ≤ t → H s ≤ᵐ[P] H t := by
    intro s t hst
    filter_upwards with ω
    have hst' : ((s + δ : ℝ≥0) : WithTop ℝ≥0) ≤ (t + δ : ℝ≥0) :=
      WithTop.coe_le_coe.mpr (add_le_add hst le_rfl)
    by_cases hs : τ ω ≤ ((s + δ : ℝ≥0) : WithTop ℝ≥0)
    · simp only [H, indicator_apply, mem_ofPred_eq, hs, hs.trans hst', if_true, le_refl]
    · simp only [H, indicator_apply, mem_ofPred_eq, hs, if_false]
      split_ifs <;> norm_num
  obtain ⟨Y, hY, hcY, heY⟩ := exists_cadlag_condExp_of_ae_monotone hF hm hr
    (integrable_const (1 : ℝ)) hb hmono
  have haC : StronglyAdapted F C := fun t ↦ stronglyMeasurable_const.indicator (hτ t)
  have hcC : HasCadlagPaths C P :=
    Eventually.of_forall (isCadlagPath_indicator_lifetime_le τ (fun _ ↦ (1 : ℝ)))
  have hlo (t) : C t ≤ᵐ[P] Y t := by
    have hiC : Integrable (C t) P :=
      (integrable_const (1 : ℝ)).indicator (F.le t _ (hτ t))
    have hCH : C t ≤ᵐ[P] H t := by
      filter_upwards with ω
      have htt : (t : WithTop ℝ≥0) ≤ (t + δ : ℝ≥0) :=
        WithTop.coe_le_coe.mpr (le_add_of_nonneg_right (show 0 ≤ δ from bot_le))
      by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
      · simp only [C, H, indicator_apply, mem_ofPred_eq, ht, ht.trans htt, if_true, le_refl]
      · simp only [C, H, indicator_apply, mem_ofPred_eq, ht, if_false]
        split_ifs <;> norm_num
    have hle := condExp_mono (m := F t) hiC (hi t) hCH
    rw [condExp_of_stronglyMeasurable (F.le t) (haC t) hiC] at hle
    exact hle.trans_eq (heY t)
  have hhi (t) : Y t ≤ᵐ[P] (fun _ ↦ (1 : ℝ)) := by
    have hle : ∀ᵐ ω ∂P, H t ω ≤ (1 : ℝ) := by
      filter_upwards [hb t] with ω hω using (le_abs_self _).trans hω
    exact (heY t).symm.trans_le (condExp_le_nonneg_const (m := F t) zero_le_one hle)
  have hlow := hcC.hasRightContinuousPaths.ae_forall_le_of_forall_ae_le
    hcY.hasRightContinuousPaths hlo
  have hhigh := hcY.hasRightContinuousPaths.ae_forall_le_of_forall_ae_le
    (Eventually.of_forall fun _ _ ↦ continuousWithinAt_const) hhi
  refine ⟨Y, hY, hcY, heY, ?_⟩
  filter_upwards [hlow, hhigh] with ω hl hu t
  exact ⟨hl t, hu t⟩

end MeasureTheory
