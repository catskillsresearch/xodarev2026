/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.FutureProbability
public import StochLean.Probability.Process.Stopping.Classification
public import StochLean.Probability.Process.Path.Subtraction

/-! # Consistent conditional stopping-window probabilities

We construct an adapted cadlag version of `P(t < τ ≤ t + δ | F_t)`.
Its bounds and vanishing after the stopping time hold simultaneously in time.
For totally inaccessible times the closed lower endpoint gives the same
coordinate conditional probabilities, because deterministic finite atoms vanish.

This establishes the version prerequisite of Protter III.10, Lemma 2, not its
uniform small-window convergence estimate.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}
  {F : MeasureTheory.Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

theorem IsTotallyInaccessibleStoppingTime.measure_eq_const
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (t : ℝ≥0) :
    P {ω | τ ω = (t : WithTop ℝ≥0)} = 0 := by
  have h := hτ.2 (fun _ ↦ (t : WithTop ℝ≥0)) (isPredictableStoppingTime_const F P t)
  have he : {ω | τ ω = (t : WithTop ℝ≥0)} =
      {ω | τ ω = (t : WithTop ℝ≥0) ∧ τ ω ≠ ⊤} := by
    ext ω
    exact ⟨fun he ↦ ⟨he, he ▸ WithTop.coe_ne_top⟩, And.left⟩
  rw [he]
  exact h

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

theorem IsStoppingTime.exists_cadlag_conditional_window (hτ : IsStoppingTime F τ)
    (hF : F.IsUsual P) (δ : ℝ≥0) :
    ∃ R : ℝ≥0 → Ω → ℝ, StronglyAdapted F R ∧ HasCadlagPaths R P ∧
      (∀ t : ℝ≥0, R t =ᵐ[P]
        P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) | F t]) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ R t ω ∧ R t ω ≤ 1 ∧
        (τ ω ≤ (t : WithTop ℝ≥0) → R t ω = 0) := by
  classical
  obtain ⟨Y, hY, hcY, heY, hbY⟩ := hτ.exists_cadlag_conditional_future hF δ
  let H : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator (fun _ ↦ 1)
  let C : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ 1)
  have haC : StronglyAdapted F C := fun t ↦ stronglyMeasurable_const.indicator (hτ t)
  have hcC : HasCadlagPaths C P :=
    Eventually.of_forall (isCadlagPath_indicator_lifetime_le τ (fun _ ↦ (1 : ℝ)))
  refine ⟨Y - C, fun t ↦ (hY.stronglyAdapted t).sub (haC t), hcY.sub hcC, ?_, ?_⟩
  · intro t
    have hiH : Integrable (H t) P :=
      (integrable_const (1 : ℝ)).indicator (F.le (t + δ) _ (hτ (t + δ)))
    have hiC : Integrable (C t) P :=
      (integrable_const (1 : ℝ)).indicator (F.le t _ (hτ t))
    have hid : H t - C t =
        {ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) := by
      funext ω
      have htt : (t : WithTop ℝ≥0) ≤ (t + δ : ℝ≥0) :=
        WithTop.coe_le_coe.mpr (le_add_of_nonneg_right (show 0 ≤ δ from bot_le))
      simp only [H, C, Pi.sub_apply, indicator_apply, mem_ofPred_eq]
      by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
      · simp only [ht, ht.trans htt, not_lt_of_ge ht, if_true, false_and, if_false, sub_self]
      · simp only [ht, lt_of_not_ge ht, if_false, true_and, sub_zero]
    have hce := condExp_sub hiH hiC (F t)
    rw [condExp_of_stronglyMeasurable (F.le t) (haC t) hiC, hid] at hce
    filter_upwards [heY t, hce] with ω he hc
    change Y t ω - C t ω = _
    change _ = P[H t | F t] ω - C t ω at hc
    exact (congrArg (fun x : ℝ ↦ x - C t ω) he.symm).trans hc.symm
  · filter_upwards [hbY] with ω hω t
    have hc0 : 0 ≤ C t ω := indicator_nonneg (fun _ _ ↦ zero_le_one) ω
    have hl := (hω t).1
    have hu := (hω t).2
    change C t ω ≤ Y t ω at hl
    change 0 ≤ Y t ω - C t ω ∧ Y t ω - C t ω ≤ 1 ∧ _
    refine ⟨sub_nonneg.mpr hl, by linarith, fun ht ↦ ?_⟩
    have heC : C t ω = 1 :=
      indicator_of_mem (s := {ω | τ ω ≤ (t : WithTop ℝ≥0)}) ht _
    change Y t ω - C t ω = 0
    linarith

theorem exists_cadlag_conditional_closed_window
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P) (δ : ℝ≥0) :
    ∃ R : ℝ≥0 → Ω → ℝ, StronglyAdapted F R ∧ HasCadlagPaths R P ∧
      (∀ t : ℝ≥0, R t =ᵐ[P]
        P[{ω | (t : WithTop ℝ≥0) ≤ τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) | F t]) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ R t ω ∧ R t ω ≤ 1 ∧
        (τ ω ≤ (t : WithTop ℝ≥0) → R t ω = 0) := by
  obtain ⟨R, ha, hc, he, hb⟩ := hτ.1.exists_cadlag_conditional_window hF δ
  refine ⟨R, ha, hc, fun t ↦ (he t).trans (condExp_congr_ae ?_), hb⟩
  have hn : ∀ᵐ ω ∂P, τ ω ≠ (t : WithTop ℝ≥0) := by
    rw [ae_iff]
    simpa only [not_not] using hτ.measure_eq_const t
  filter_upwards [hn] with ω hω
  have hl : (t : WithTop ℝ≥0) < τ ω ↔ (t : WithTop ℝ≥0) ≤ τ ω :=
    lt_iff_le_and_ne.trans (and_iff_left hω.symm)
  simp only [indicator_apply, mem_ofPred_eq, hl]

end MeasureTheory
