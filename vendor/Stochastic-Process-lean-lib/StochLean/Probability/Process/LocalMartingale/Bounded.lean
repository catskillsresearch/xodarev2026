/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Dominated local martingales are martingales

The proof takes limits in the defining set-integral identities of the masked
fundamental sequence. Thus it does not require continuous-time optional
sampling or a semimartingale decomposition.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}

/-- At a fixed finite time the masked localizations eventually equal the original process. -/
theorem IsPreLocalizingSequence.ae_eventually_masked_stoppedProcess_eq
    (hτ : IsPreLocalizingSequence F τ P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n) t ω = X t ω := by
  filter_upwards [hτ.tendsto_top] with ω hω
  have he := hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
  filter_upwards [he] with n hn
  have hpos : 0 < τ n ω := lt_of_le_of_lt bot_le hn
  rw [stoppedProcess_eq_of_le hn.le,
    indicator_of_mem (show ω ∈ {ω | 0 < τ n ω} from hpos)]

/-- Protter I.51 in integrable-envelope form. A separate common-event bound is allowed
on each compact horizon. In particular no globally integrable running maximum is required. -/
theorem IsLocalMartingale.martingale_of_integrable_envelope
    [SigmaFiniteFiltration P F] (hX : IsLocalMartingale X F P)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ R ω) : Martingale X F P := by
  choose R hR hb using hdom
  obtain ⟨τ, hτ⟩ := hX.2.2
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  have hYm : ∀ n, Martingale (Y n) F P := fun n ↦ (hτ.2.2 n).1
  have hYbound : ∀ n t, ∀ᵐ ω ∂P, ‖Y n t ω‖ ≤ R t ω := by
    intro n t
    filter_upwards [hb t] with ω hω
    change ‖stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n) t ω‖ ≤ R t ω
    rw [stoppedProcess_indicator_comm]
    exact (norm_indicator_le_norm_self _ _).trans
      (hω _ (WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ n ω))))
  have hXint : ∀ t, Integrable (X t) P := fun t ↦ (hR t).mono'
    ((hX.1 t).mono (F.le t) le_rfl).aestronglyMeasurable
    ((hb t).mono fun _ hω ↦ hω t le_rfl)
  have hconv : ∀ t A, Tendsto (fun n ↦ ∫ ω in A, Y n t ω ∂P) atTop
      (𝓝 (∫ ω in A, X t ω ∂P)) := by
    intro t A
    apply tendsto_integral_of_dominated_convergence (R t)
    · intro n
      exact ((hYm n).stronglyAdapted t).mono (F.le t) |>.aestronglyMeasurable.restrict
    · exact (hR t).integrableOn
    · intro n
      exact ae_restrict_of_ae (hYbound n t)
    · apply ae_restrict_of_ae
      filter_upwards [hτ.1.ae_eventually_masked_stoppedProcess_eq (X := X) t] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      exact hn.symm
  refine ⟨hX.1.stronglyAdapted, fun s t hst ↦ ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hXint t)
    (fun _ _ _ ↦ (hXint s).integrableOn) ?_
    (hX.1.stronglyAdapted s).aestronglyMeasurable).symm
  intro A hA _
  have heq : (fun n ↦ ∫ ω in A, Y n s ω ∂P) = fun n ↦ ∫ ω in A, Y n t ω ∂P :=
    funext fun n ↦ (hYm n).setIntegral_eq hst hA
  exact tendsto_nhds_unique (hconv s A) (heq ▸ hconv t A)

/-- Klenke 21.68, with the common-event bound required for random stopped evaluation. -/
theorem IsLocalMartingale.martingale_of_bound [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
    (hX : IsLocalMartingale X F P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ C) : Martingale X F P :=
  hX.martingale_of_integrable_envelope fun _ ↦
    ⟨fun _ ↦ C, integrable_const _, hb.mono fun _ hω t _ ↦ hω t⟩

/-- The global envelope version of Protter I.51 gives deterministic-time UI as well. -/
theorem IsLocalMartingale.isUIMartingale_of_integrable_envelope
    [SigmaFiniteFiltration P F] (hX : IsLocalMartingale X F P)
    {R : Ω → ℝ} (hR : Integrable R P)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ R ω) : IsUIMartingale X F P := by
  have hm := hX.martingale_of_integrable_envelope fun _ ↦
    ⟨R, hR, hb.mono fun _ hω t _ ↦ hω t⟩
  refine ⟨hm, ?_⟩
  have hu : UniformIntegrable (fun _ : ℝ≥0 ↦ R) 1 P :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hR)
  apply hu.mono_norm (fun t ↦ (hm.integrable t).aestronglyMeasurable)
  intro t
  filter_upwards [hb] with ω hω
  exact (hω t).trans (le_abs_self _)

theorem IsLocalMartingale.isUIMartingale_of_bound [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
    (hX : IsLocalMartingale X F P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ C) : IsUIMartingale X F P :=
  hX.isUIMartingale_of_integrable_envelope (integrable_const (C : ℝ)) hb

end ProbabilityTheory
