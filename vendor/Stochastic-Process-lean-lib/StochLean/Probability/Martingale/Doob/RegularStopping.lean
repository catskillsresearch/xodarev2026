/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.JumpSampling
public import StochLean.Probability.Process.Stopping.TerminalRestriction
public import StochLean.Probability.Process.Stopping.BeforeSigmaOrder
public import StochLean.Probability.Process.Stopping.PredictableRestriction

/-! # Predictable jump-mean regularity survives stopping

For a predictable test lifetime gamma and an arbitrary stopping time tau,
the event `gamma <= tau` belongs to the field before gamma. Restricting gamma
to this event preserves predictability. The actual jump-sampling identity
therefore transfers the original zero-mean test to the stopped process.
No assertion that an amplitude-selected jump remains centered is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ γ : Ω → WithTop ℝ≥0}

/-- Arbitrary stopping preserves the zero means of positive predictable
jumps. Infinity is the explicit zero terminal, and the stopping endpoint is retained. -/
theorem HasCadlagPaths.integral_stopped_jump_stoppedProcess_eq_zero
    (hc : HasCadlagPaths X P) (hF : F.IsUsual P) (hτ : IsStoppingTime F τ)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (hγ : IsPredictableStoppingTime F γ P) (hpos : ∀ᵐ ω ∂P, 0 < γ ω) :
    (∫ ω, stoppedValueWithTerminal (jumpProcess (MeasureTheory.stoppedProcess X τ))
      (fun _ ↦ (0 : ℝ)) γ ω ∂P) = 0 := by
  let A : Set Ω := {ω | γ ω ≤ τ ω}
  have hA : MeasurableSet[hγ.1.measurableSpaceBefore] A := by
    simpa only [compl_ofPred, not_lt] using (hτ.measurableSet_lt_before hγ.1).compl
  have hp := hγ.restrictedStoppingTime_before hF hA
  have hpositive : ∀ᵐ ω ∂P, 0 < restrictedStoppingTime γ A ω := by
    filter_upwards [hpos] with ω hω
    by_cases hAω : ω ∈ A
    · rw [restrictedStoppingTime_of_mem γ hAω]
      exact hω
    · rw [restrictedStoppingTime_of_notMem γ hAω]
      exact WithTop.coe_lt_top 0
  have he : stoppedValueWithTerminal (jumpProcess (MeasureTheory.stoppedProcess X τ))
      (fun _ ↦ (0 : ℝ)) γ =ᵐ[P]
      stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
        (restrictedStoppingTime γ A) := by
    rw [stoppedValueWithTerminal_zero_restrictedStoppingTime]
    simpa only [indicator_univ] using
      hc.ae_stoppedValueWithTerminal_jump_masked_stoppedProcess univ τ γ
  exact (integral_congr_ae he).trans (hreg _ hp hpositive)

end ProbabilityTheory
