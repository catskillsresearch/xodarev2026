/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalWindowOrder
public import StochLean.Probability.Process.Stopping.ConditionalBoundedSampling
public import StochLean.Probability.Process.Path.LifetimeWindow

/-! # Conditional stopping windows at bounded stopping times

Every adapted right-continuous version of the deterministic-time conditional
window has the correct conditional value at a bounded stopping time. Common
bounds are derived from version uniqueness, not assumed for arbitrary
conditional-expectation representatives.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {δ : ℝ≥0}

theorem conditional_window_sample (hτ : IsStoppingTime F τ) (hF : F.IsUsual P)
    (haR : StronglyAdapted F R) (hrR : HasRightContinuousPaths R P)
    (heR : ∀ t : ℝ≥0, R t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t])
    (σ : FiniteStoppingTime F) {T : ℝ≥0} (hσ : ∀ ω, σ ω ≤ T) :
    (fun ω ↦ R (σ ω) ω) =ᵐ[P]
      P[{ω | (σ ω : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | σ.measurableSpace] := by
  let X : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ))
  have hmX : Measurable (Function.uncurry X) :=
    measurable_indicator_lifetime_window τ δ (hτ.measurable.mono hτ.measurableSpace_le le_rfl)
  have hrX : HasRightContinuousPaths X P :=
    Eventually.of_forall (isRightContinuousPath_indicator_lifetime_window τ δ)
  have hbX : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ (1 : ℝ) := by
    filter_upwards with ω t
    exact (norm_indicator_le_norm_self (fun _ : Ω ↦ (1 : ℝ)) ω).trans_eq (norm_one (α := ℝ))
  obtain ⟨Q, _, hcQ, heQ, hbQ⟩ := hτ.exists_cadlag_conditional_window hF δ
  have hind := cadlag_conditional_window_unique hrR hcQ.hasRightContinuousPaths heR heQ
  have hbR : ∀ᵐ ω ∂P, ∀ t, ‖R t ω‖ ≤ (1 : ℝ) := by
    filter_upwards [hind, hbQ] with ω hω hb t
    rw [hω t, Real.norm_eq_abs, abs_of_nonneg (hb t).1]
    exact (hb t).2.1
  have hs := σ.sample_condExp_of_dominated_rightContinuous_of_usual hσ hF hmX haR hrX hrR
    (integrable_const (1 : ℝ)) hbX hbR heR
  have hid : (fun ω ↦ X (σ ω) ω) =
      {ω | (σ ω : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp only [X, indicator_apply, mem_ofPred_eq]
  rw [hid] at hs
  exact hs

theorem conditional_window_setIntegral_sample (hτ : IsStoppingTime F τ) (hF : F.IsUsual P)
    (haR : StronglyAdapted F R) (hrR : HasRightContinuousPaths R P)
    (heR : ∀ t : ℝ≥0, R t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t])
    (σ : FiniteStoppingTime F) {T : ℝ≥0} (hσ : ∀ ω, σ ω ≤ T)
    {A : Set Ω} (hA : MeasurableSet[σ.measurableSpace] A) :
    (∫ ω in A, R (σ ω) ω ∂P) =
      P.real (A ∩ {ω | (σ ω : WithTop ℝ≥0) < τ ω ∧
        τ ω ≤ ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0)}) := by
  have hs := conditional_window_sample hτ hF haR hrR heR σ hσ
  have hmτ : Measurable τ := hτ.measurable.mono hτ.measurableSpace_le le_rfl
  have hmσ : Measurable σ :=
    (σ.isStoppingTime.measurable.untopD 0).mono σ.measurableSpace_le le_rfl
  have hmW : MeasurableSet {ω | (σ ω : WithTop ℝ≥0) < τ ω ∧
      τ ω ≤ ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0)} :=
    (measurableSet_lt (WithTop.measurable_coe.comp hmσ) hmτ).inter
      (measurableSet_le hmτ (WithTop.measurable_coe.comp (hmσ.add measurable_const)))
  have hi := (integrable_const (1 : ℝ) : Integrable (fun _ : Ω ↦ (1 : ℝ)) P).indicator hmW
  rw [integral_congr_ae (ae_restrict_of_ae hs),
    setIntegral_condExp σ.measurableSpace_le hi hA, integral_indicator hmW,
    Measure.restrict_restrict hmW, inter_comm]
  simp

theorem conditional_window_threshold_measure_le (hτ : IsStoppingTime F τ) (hF : F.IsUsual P)
    (haR : StronglyAdapted F R) (hrR : HasRightContinuousPaths R P)
    (heR : ∀ t : ℝ≥0, R t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t])
    (σ : FiniteStoppingTime F) {T : ℝ≥0} (hσ : ∀ ω, σ ω ≤ T)
    {A : Set Ω} (hA : MeasurableSet[σ.measurableSpace] A)
    {a : ℝ} (htrigger : ∀ᵐ ω ∂P, ω ∈ A → a ≤ R (σ ω) ω) :
    a * P.real A ≤ P.real (A ∩ {ω | (σ ω : WithTop ℝ≥0) < τ ω ∧
      τ ω ≤ ((σ ω + δ : ℝ≥0) : WithTop ℝ≥0)}) := by
  have hs := conditional_window_sample hτ hF haR hrR heR σ hσ
  have hi : Integrable (fun ω ↦ R (σ ω) ω) P := integrable_condExp.congr hs.symm
  have hle : (∫ _ω in A, a ∂P) ≤ ∫ ω in A, R (σ ω) ω ∂P :=
    integral_mono_ae (integrable_const a) hi.restrict
      ((ae_restrict_iff' (σ.measurableSpace_le _ hA)).mpr htrigger)
  rw [conditional_window_setIntegral_sample hτ hF haR hrR heR σ hσ hA] at hle
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]
    using hle

end MeasureTheory
