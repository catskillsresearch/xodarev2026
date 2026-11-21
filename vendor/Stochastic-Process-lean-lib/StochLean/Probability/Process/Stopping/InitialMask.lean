/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Stopping

/-! # Composition of the masked stopping operation

Both initial-event masks are retained, including when either stopping time is zero.
The identity is pointwise and needs no stopping-time or measurability premise.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

theorem masked_stoppedProcess_masked_stoppedProcess {Ω E : Type*} [Zero E]
    (X : ℝ≥0 → Ω → E) (σ τ : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator
      (stoppedProcess (fun u ↦ {ω | 0 < τ ω}.indicator (X u)) τ t)) σ =
      stoppedProcess (fun t ↦ {ω | 0 < min σ τ ω}.indicator (X t)) (min σ τ) := by
  simp_rw [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess,
    Set.indicator_indicator]
  have hset : {ω | 0 < σ ω} ∩ {ω | 0 < τ ω} = {ω | 0 < min σ τ ω} := by
    ext ω
    change (0 < σ ω ∧ 0 < τ ω) ↔ 0 < min (σ ω) (τ ω)
    exact lt_min_iff.symm
  rw [hset]

end ProbabilityTheory
