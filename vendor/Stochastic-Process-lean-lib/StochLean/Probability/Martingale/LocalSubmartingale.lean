/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.MonotonePaths
public import StochLean.Probability.Process.LocalMartingale.ContinuousSquareLocalization

/-! # Local submartingale witnesses and integrable-envelope promotion

Locality is Mathlib's `Locally`, including its initial-event masks. There is
no new local-submartingale hierarchy. A continuous increasing zero-initial
drift can be added to any existing cadlag local martingale. Promotion to a
true submartingale requires compact-horizon integrable domination.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {M A X : ℝ≥0 → Ω → ℝ}

theorem IsLocalMartingale.locally_submartingale_add_of_monotone
    [IsFiniteMeasure P] (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (ha : Adapted F A) (hc : HasContinuousPaths A P) (hm : HasMonotonePaths A P)
    (h0 : A 0 =ᵐ[P] 0) : Locally (fun Y ↦ Submartingale Y F P) F (M + A) P := by
  obtain ⟨τ, hτ⟩ := hM.2.2
  obtain ⟨σ, hσ, hσm, hb⟩ := ha.exists_bounded_stoppingSequence hF hc 0
    (h0.mono fun _ hω ↦ by simp only [hω, Pi.zero_apply, norm_zero, NNReal.coe_zero, le_refl])
  let ρ := min τ σ
  have hρ : IsFundamentalSequence M F P ρ := hτ.min_other hM.2.1 hF hσ hσm
  refine ⟨ρ, hρ.isLocalizingSequence, fun n ↦ ?_⟩
  let B := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (A t)) (ρ n)
  have hmask : MeasurableSet[F 0] {ω | 0 < ρ n ω} := by
    simpa only [WithTop.coe_zero, Set.compl_ofPred, not_le] using
      (hρ.1.isStoppingTime n 0).compl
  have haB : Adapted F B :=
    (show Adapted F (fun t ↦ {ω | 0 < ρ n ω}.indicator (A t)) from
      fun t ↦ (ha t).indicator (F.mono bot_le _ hmask)).stronglyAdapted.stoppedProcess_of_usual
        hF (hc.hasCadlagPaths.indicator _).hasRightContinuousPaths (hρ.1.isStoppingTime n)
      |>.adapted
  have hbB : ∀ t, ∀ᵐ ω ∂P, ‖B t ω‖ ≤ (n : ℝ) := by
    intro t
    filter_upwards [hb n] with ω hω
    change ‖MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < ρ n ω}.indicator (A t)) (ρ n) t ω‖ ≤ _
    rw [stoppedProcess_indicator_comm]
    apply (norm_indicator_le_norm_self _ _).trans
    let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (ρ n ω)).untopA
    have hne : min (t : WithTop ℝ≥0) (ρ n ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hu : (u : WithTop ℝ≥0) ≤ σ n ω := by
      dsimp only [u]
      rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
      exact (min_le_right _ _).trans (min_le_right _ _)
    change ‖A u ω‖ ≤ (n : ℝ)
    simpa only [stoppedProcess_eq_of_le hu, NNReal.coe_zero, zero_add] using hω u
  have hiB : ∀ t, Integrable (B t) P := fun t ↦
    (integrable_const (n : ℝ)).mono'
      ((haB t).mono (F.le t) le_rfl).aestronglyMeasurable (hbB t)
  have hmB : HasMonotonePaths B P := (hm.indicator _).stoppedProcess _
  have hsum := ((hρ.2.2 n).1.submartingale).add (hmB.submartingale haB hiB)
  convert hsum using 1
  ext t ω
  change MeasureTheory.stoppedProcess
    (fun i ↦ {ω | 0 < ρ n ω}.indicator ((M + A) i)) (ρ n) t ω = _
  simp only [B, MeasureTheory.stoppedProcess, Pi.add_apply, Set.indicator_add']

theorem submartingale_of_locally_submartingale_of_integrable_envelope
    [SigmaFiniteFiltration P F] (ha : Adapted F X)
    (hX : Locally (fun Y ↦ Submartingale Y F P) F X P)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ R ω) : Submartingale X F P := by
  choose R hR hb using hdom
  obtain ⟨τ, hτ, hYm⟩ := hX
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n)
  have hYbound : ∀ n t, ∀ᵐ ω ∂P, ‖Y n t ω‖ ≤ R t ω := by
    intro n t
    filter_upwards [hb t] with ω hω
    change ‖stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n) t ω‖ ≤ _
    rw [stoppedProcess_indicator_comm]
    exact (norm_indicator_le_norm_self _ _).trans
      (hω _ (WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ n ω))))
  have hi : ∀ t, Integrable (X t) P := fun t ↦ (hR t).mono'
    ((ha t).mono (F.le t) le_rfl).aestronglyMeasurable
    ((hb t).mono fun _ hω ↦ hω t le_rfl)
  have hconv : ∀ t C, Tendsto (fun n ↦ ∫ ω in C, Y n t ω ∂P) atTop
      (𝓝 (∫ ω in C, X t ω ∂P)) := by
    intro t C
    apply tendsto_integral_of_dominated_convergence (R t)
    · intro n
      exact ((hYm n).stronglyAdapted t).mono (F.le t) |>.aestronglyMeasurable.restrict
    · exact (hR t).integrableOn
    · exact fun n ↦ ae_restrict_of_ae (hYbound n t)
    · apply ae_restrict_of_ae
      filter_upwards [hτ.toIsPreLocalizingSequence.ae_eventually_masked_stoppedProcess_eq
        (X := X) t] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      exact hn.symm
  apply submartingale_of_setIntegral_le ha.stronglyAdapted hi
  intro s t hst C hC
  exact le_of_tendsto_of_tendsto (hconv s C) (hconv t C)
    (Eventually.of_forall fun n ↦ (hYm n).setIntegral_le hst hC)

end ProbabilityTheory
