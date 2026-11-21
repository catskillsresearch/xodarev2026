/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.TerminalValue
public import StochLean.Probability.Process.Stopping.Restriction

/-! # Explicit zero-terminal sampling at a restricted lifetime

Restriction sends the complementary event to infinity. An explicitly zero
terminal therefore gives an actual indicator identity, without evaluating
the original process at an artificial finite value for infinity.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} [Zero E]

/-- Restricting a lifetime masks its actual zero-terminal sample. No
measurability, path regularity or finiteness assumption is needed. -/
theorem stoppedValueWithTerminal_zero_restrictedStoppingTime
    (X : ℝ≥0 → Ω → E) (τ : Ω → WithTop ℝ≥0) (A : Set Ω) :
    stoppedValueWithTerminal X (fun _ ↦ 0) (restrictedStoppingTime τ A) =
      A.indicator (stoppedValueWithTerminal X (fun _ ↦ 0) τ) := by
  classical
  funext ω
  by_cases hω : ω ∈ A
  · simp only [stoppedValueWithTerminal, stoppedValue,
      restrictedStoppingTime_of_mem τ hω, indicator_of_mem hω]
  · rw [stoppedValueWithTerminal_of_top (restrictedStoppingTime_of_notMem τ hω),
      indicator_of_notMem hω]

end MeasureTheory
