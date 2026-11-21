/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.BoundedLocalization
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import StochLean.Probability.Process.Stopping.Usual

/-! # Bounded localization up to a random lifetime

The witness form of corrected Klenke 21.67 also applies when the limiting time is not infinity.
There is no second local-martingale hierarchy: the input and output are actual stopping sequences.
The limiting random time need not be integrable or finite. The initial bound is indispensable.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

/-- Refine any true-martingale localizing witness up to `κ` to bounded UI martingales,
without replacing its random lifetime by infinity. -/
theorem exists_bounded_martingale_localizations_upTo
    (hX : Adapted F X) (hc : HasContinuousPaths X P) (hF : F.IsUsual P)
    {τ : ℕ → Ω → WithTop ℝ≥0} {κ : Ω → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime F (τ n)) (hmono : Monotone τ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 (κ ω)))
    (hm : ∀ n, Martingale (stoppedProcess X (τ n)) F P)
    (C : ℝ≥0) (hzero : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ C) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime F (σ n)) ∧ Monotone σ ∧
      (∀ n, σ n ≤ τ n) ∧ (∀ᵐ ω ∂P, Tendsto (σ · ω) atTop (𝓝 (κ ω))) ∧
      ∀ n, IsUIMartingale (stoppedProcess X (σ n)) F P ∧
        (∀ᵐ ω ∂P, ∀ t, ‖stoppedProcess X (σ n) t ω‖ ≤ (C : ℝ) + n) ∧
        IsSquareIntegrableMartingale (stoppedProcess X (σ n)) F P := by
  obtain ⟨ρ, hρ, hρmono, hb⟩ := hX.exists_bounded_stoppingSequence hF hc C hzero
  let σ : ℕ → Ω → WithTop ℝ≥0 := τ ⊓ ρ
  have hσ : ∀ n, IsStoppingTime F (σ n) := fun n ↦ (hτ n).min (hρ.isStoppingTime n)
  have hσlim : ∀ᵐ ω ∂P, Tendsto (σ · ω) atTop (𝓝 (κ ω)) := by
    filter_upwards [hlim, hρ.tendsto_top] with ω hω hρω
    simpa only [σ, Pi.inf_apply, min_eq_left le_top] using hω.min hρω
  have hσm : ∀ n, Martingale (stoppedProcess X (σ n)) F P := by
    intro n
    simpa only [stoppedProcess_stoppedProcess, σ, Pi.inf_apply, inf_comm] using
      (hm n).stoppedProcess_of_usual hF (hc.stoppedProcess (τ n)).hasRightContinuousPaths
        (hρ.isStoppingTime n)
  have hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t, ‖stoppedProcess X (σ n) t ω‖ ≤ (C : ℝ) + n := by
    intro n
    have heq : stoppedProcess X (σ n) = stoppedProcess (stoppedProcess X (ρ n)) (τ n) := by
      simp only [stoppedProcess_stoppedProcess, σ, Pi.inf_apply]
    rw [heq]
    filter_upwards [hb n] with ω hω t
    exact hω _
  refine ⟨σ, hσ, hmono.inf hρmono, fun _ _ ↦ min_le_left _ _, hσlim, fun n ↦ ?_⟩
  have hlocal := (hσm n).isLocalMartingale (hc.stoppedProcess (σ n)).hasCadlagPaths
  refine ⟨hlocal.isUIMartingale_of_bound (C + n) (hbound n), hbound n, hσm n, fun t ↦ ?_⟩
  exact MemLp.of_bound ((hσm n).integrable t).aestronglyMeasurable ((C : ℝ) + n)
    ((hbound n).mono fun _ hω ↦ hω t)

/-- Source-strength AE monotonicity suffices: it is repaired on one initial null event before
constructing the pointwise-monotone witness. -/
theorem exists_bounded_martingale_localizations_upTo_of_ae_monotone
    (hX : Adapted F X) (hc : HasContinuousPaths X P) (hF : F.IsUsual P)
    {τ : ℕ → Ω → WithTop ℝ≥0} {κ : Ω → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime F (τ n)) (hmono : ∀ᵐ ω ∂P, Monotone (τ · ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 (κ ω)))
    (hm : ∀ n, Martingale (stoppedProcess X (τ n)) F P)
    (C : ℝ≥0) (hzero : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ C) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime F (σ n)) ∧ Monotone σ ∧
      (∀ n, σ n ≤ τ n) ∧ (∀ᵐ ω ∂P, Tendsto (σ · ω) atTop (𝓝 (κ ω))) ∧
      ∀ n, IsUIMartingale (stoppedProcess X (σ n)) F P ∧
        (∀ᵐ ω ∂P, ∀ t, ‖stoppedProcess X (σ n) t ω‖ ≤ (C : ℝ) + n) ∧
        IsSquareIntegrableMartingale (stoppedProcess X (σ n)) F P := by
  obtain ⟨ρ, hρmono, hρ, hρle, heq⟩ := exists_monotone_stoppingSequence_version hF hτ hmono
  have hρlim : ∀ᵐ ω ∂P, Tendsto (ρ · ω) atTop (𝓝 (κ ω)) := by
    filter_upwards [hlim, heq] with ω hω heω
    simpa only [← heω] using hω
  have hρm : ∀ n, Martingale (stoppedProcess X (ρ n)) F P := by
    intro n
    apply (hm n).congr (hX.stronglyAdapted.stoppedProcess_of_usual hF
      hc.hasRightContinuousPaths (hρ n))
    intro t
    filter_upwards [heq] with ω hω
    simp only [stoppedProcess, hω n]
  obtain ⟨σ, hσ, hσmono, hσle, hσlim, hb⟩ :=
    exists_bounded_martingale_localizations_upTo hX hc hF hρ hρmono hρlim hρm C hzero
  exact ⟨σ, hσ, hσmono, fun n ↦ (hσle n).trans (hρle n), hσlim, hb⟩

end ProbabilityTheory
