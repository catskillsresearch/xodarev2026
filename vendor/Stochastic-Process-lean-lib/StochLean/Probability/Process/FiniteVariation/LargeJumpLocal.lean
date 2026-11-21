/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.LargeJumpIntegrable
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableAlgebra
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableLocalization
public import StochLean.Probability.Process.Path.LargeJumpStopping
public import StochLean.Probability.Process.LocalMartingale

/-! # Locally integrable large-jump sums of a local martingale

The original fundamental sequence gives true martingales after positive-lifetime
masking and stopping. Their actual signed and norm large-jump sums have locally
integrable variation by the true-martingale result. Exact event restriction and
the common-event stopped-sum identity identify these with the native masked
stoppings of the original sums. Stable-bundle localization idempotence then
gives locally integrable variation of those original cumulative processes.

No semimartingale representation, new localizing selector, source moment bound,
or integrability of the initial random value is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- Both actual large-jump cumulative processes of a general local martingale
have locally integrable variation, with no initial integrability assumption. -/
theorem IsLocalMartingale.hasLocallyIntegrableVariation_largeJumpSumProcesses
    (hM : IsLocalMartingale X F P) (hF : F.IsUsual P) (hb : 0 < b) :
    HasLocallyIntegrableVariation (largeJumpSumProcess X b) F P ∧
      HasLocallyIntegrableVariation (largeJumpNormSumProcess X b) F P := by
  obtain ⟨haA, haC⟩ := hM.1.stronglyAdapted_largeJumpSumProcesses_of_usual hF hM.2.1 hb
  obtain ⟨hcA, hcC, _⟩ := hM.2.1.largeJumpSumProcesses_properties hb
  obtain ⟨τ, hτ⟩ := hM.2.2
  have hlocal (n : ℕ) :
      HasLocallyIntegrableVariation (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ n ω}.indicator (largeJumpSumProcess X b t)) (τ n)) F P ∧
      HasLocallyIntegrableVariation (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ n ω}.indicator (largeJumpNormSumProcess X b t)) (τ n)) F P := by
    have hcMask := hM.2.1.indicator {ω | 0 < τ n ω}
    have hv := (hτ.2.2 n).1.hasLocallyIntegrableVariation_largeJumpSumProcesses
      hF (hcMask.stoppedProcess (τ n)) hb
    have heA := hcMask.largeJumpSumProcess_stoppedProcess b (τ n)
    have heC := hcMask.largeJumpNormSumProcess_stoppedProcess b (τ n)
    rw [largeJumpSumProcess_indicator] at heA
    rw [largeJumpNormSumProcess_indicator] at heC
    exact ⟨hv.1.congr heA, hv.2.congr heC⟩
  exact ⟨hasLocallyIntegrableVariation_of_locally hF haA.adapted hcA
      ⟨τ, hτ.isLocalizingSequence, fun n ↦ (hlocal n).1⟩,
    hasLocallyIntegrableVariation_of_locally hF haC.adapted hcC
      ⟨τ, hτ.isLocalizingSequence, fun n ↦ (hlocal n).2⟩⟩

end ProbabilityTheory
