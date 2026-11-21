/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.BoundedLocalization
public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.Probability.Process.LocalMartingale.Stability
public import StochLean.Probability.Process.LocalMartingale.InitialValue

/-! # Bounded localization of continuous local martingales

Klenke 21.67 is used with its necessary initial-value guard. Closed-level hitting times of an
everywhere-continuous indistinguishable version give actual monotone localizers. The original
process is bounded after stopping on one common full-measure event, not just at fixed times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

/-- Bounded initial values permit unmasked bounded, UI, finite-time L2 localizations. -/
theorem IsContinuousLocalMartingale.exists_bounded_klenkeLocalizingSequence
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) (C : ℝ≥0)
    (hzero : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ C) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsKlenkeLocalizingSequence X F P τ ∧
      ∀ n, (∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess X (τ n) t ω‖ ≤ (C : ℝ) + n) ∧
        IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess X (τ n)) F P := by
  obtain ⟨τ, hτ, hmono, hb⟩ := hX.1.1.exists_bounded_stoppingSequence hF hX.2 C hzero
  have hui : ∀ n, IsUIMartingale (MeasureTheory.stoppedProcess X (τ n)) F P := fun n ↦
    (hX.1.stoppedProcess hF (hτ.isStoppingTime n)).isUIMartingale_of_bound (C + n) (hb n)
  refine ⟨τ, ⟨hτ, hmono, hui⟩, fun n ↦ ⟨hb n, (hui n).1, ?_⟩⟩
  intro t
  exact MemLp.of_bound ((hui n).1.integrable t).aestronglyMeasurable ((C : ℝ) + n)
    ((hb n).mono fun _ hω ↦ hω t)

/-- Centering preserves the canonical local-martingale predicate even for nonintegrable
initial values: the time-constant initial process is localized using the Protter mask. -/
theorem IsContinuousLocalMartingale.sub_initial (hX : IsContinuousLocalMartingale X F P)
    (hF : F.IsUsual P) :
    IsContinuousLocalMartingale (fun t ω ↦ X t ω - X 0 ω) F P := by
  refine ⟨hX.1.sub (isContinuousLocalMartingale_const_initial (hX.1.1 0)).1 hF, ?_⟩
  filter_upwards [hX.2] with ω hω
  exact hω.sub continuous_const

/-- The corrected centered form of Klenke 21.67, without any integrability assumption on `X 0`. -/
theorem IsContinuousLocalMartingale.exists_bounded_centered_localizingSequence
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0,
      IsKlenkeLocalizingSequence (fun t ω ↦ X t ω - X 0 ω) F P τ ∧
      ∀ n, (∀ᵐ ω ∂P, ∀ t,
        ‖MeasureTheory.stoppedProcess (fun s ω ↦ X s ω - X 0 ω) (τ n) t ω‖ ≤ (n : ℝ)) ∧
        IsSquareIntegrableMartingale
          (MeasureTheory.stoppedProcess (fun s ω ↦ X s ω - X 0 ω) (τ n)) F P := by
  simpa only [NNReal.coe_zero, zero_add] using
    (hX.sub_initial hF).exists_bounded_klenkeLocalizingSequence hF 0
      (ae_of_all _ fun _ ↦ by simp)

end ProbabilityTheory
