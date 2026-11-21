/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalWindowOrder

/-! # Coherent decreasing sequences of conditional windows

Individual cadlag versions are constructed first. Their countably many path,
bound and order events are then intersected and reset on one initial null
event. The resulting versions are everywhere cadlag and pointwise ordered,
so their first-hitting times can be compared pointwise as stopping witnesses.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

theorem IsStoppingTime.exists_coherent_conditional_windows (hτ : IsStoppingTime F τ)
    (hF : F.IsUsual P) (δ : ℕ → ℝ≥0) (hδ : Antitone δ) :
    ∃ R : ℕ → ℝ≥0 → Ω → ℝ,
      (∀ n, StronglyAdapted F (R n)) ∧
      (∀ n ω, IsCadlagPath (fun t ↦ R n t ω)) ∧
      (∀ n (t : ℝ≥0), R n t =ᵐ[P]
        P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ n : ℝ≥0) : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) | F t]) ∧
      (∀ ω n (t : ℝ≥0), 0 ≤ R n t ω ∧ R n t ω ≤ 1 ∧
        (τ ω ≤ (t : WithTop ℝ≥0) → R n t ω = 0)) ∧
      ∀ ω t, Antitone (fun n ↦ R n t ω) := by
  classical
  choose Q ha hc he hb using fun n ↦ hτ.exists_cadlag_conditional_window hF (δ n)
  have hord (n) : ∀ᵐ ω ∂P, ∀ t, Q (n + 1) t ω ≤ Q n t ω :=
    cadlag_conditional_window_ae_le hτ (hδ (Nat.le_succ n))
      (hc (n + 1)).hasRightContinuousPaths (hc n).hasRightContinuousPaths (he (n + 1)) (he n)
  let G : Set Ω := {ω | (∀ n, IsCadlagPath (fun t ↦ Q n t ω)) ∧
    (∀ n (t : ℝ≥0), 0 ≤ Q n t ω ∧ Q n t ω ≤ 1 ∧
      (τ ω ≤ (t : WithTop ℝ≥0) → Q n t ω = 0)) ∧
    ∀ n t, Q (n + 1) t ω ≤ Q n t ω}
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [ae_all_iff.mpr hc, ae_all_iff.mpr hb, ae_all_iff.mpr hord] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hG : MeasurableSet[F 0] G := by
    have hGc : MeasurableSet[F 0] Gᶜ := hF.complete_initial _ (ae_iff.mp hGae)
    simpa only [compl_compl] using hGc.compl
  let R : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦ if ω ∈ G then Q n t ω else 0
  refine ⟨R, fun n t ↦ Measurable.stronglyMeasurable
    (Measurable.ite (F.mono bot_le _ hG) (ha n t).measurable measurable_const), ?_, ?_, ?_, ?_⟩
  · intro n ω
    by_cases hω : ω ∈ G
    · simpa only [R, if_pos hω] using hω.1 n
    · simp only [R, if_neg hω]
      exact IsContinuousPath.isCadlagPath continuous_const
  · intro n t
    filter_upwards [hGae, he n t] with ω hω hnt
    exact (if_pos hω).trans hnt
  · intro ω n t
    by_cases hω : ω ∈ G
    · simpa only [R, if_pos hω] using hω.2.1 n t
    · simp only [R, if_neg hω, le_refl, zero_le_one, implies_true, and_self]
  · intro ω t
    apply antitone_nat_of_succ_le
    intro n
    by_cases hω : ω ∈ G
    · simpa only [R, if_pos hω] using hω.2.2 n t
    · simp only [R, if_neg hω, le_refl]

end MeasureTheory
