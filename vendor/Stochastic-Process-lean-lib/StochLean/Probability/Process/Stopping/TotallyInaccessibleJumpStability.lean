/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.TotallyInaccessibleJumps
public import StochLean.Probability.Process.Path.JumpStopping

/-! # Totally inaccessible jumps under stopping

Stopping a cadlag path preserves each jump at or before the cutoff and removes
the later jumps. Thus the original countable covering sequence still covers
the stopped process's nonzero positive-time jump graph. The cutoff need not be
a stopping time: the conclusion concerns only the jump-coverage predicate.

The source stopped-process convention retains the jump at a finite cutoff,
leaves the path unchanged for an infinite cutoff, and retains the original
initial value at a zero cutoff. The positive-time coverage condition does not
impose any restriction on that initial value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Arbitrary pathwise stopping preserves the totally inaccessible positive-time
jump-coverage property of a process with almost-sure cadlag paths. -/
theorem HasTotallyInaccessibleJumps.stoppedProcess
    (hJ : HasTotallyInaccessibleJumps F X P) (hc : HasCadlagPaths X P)
    (τ : Ω → WithTop ℝ≥0) :
    HasTotallyInaccessibleJumps F (MeasureTheory.stoppedProcess X τ) P := by
  obtain ⟨σ, hσ, hcover⟩ := hJ
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hc, hcover] with ω hcω hω
  intro t ht hj
  apply hω t ht
  intro hz
  apply hj
  rw [hcω.jumpProcess_stoppedProcess τ t, hz]
  simp only [ite_self]

end ProbabilityTheory
