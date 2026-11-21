/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Algebra
public import StochLean.Probability.Process.UCP.Stopping

/-! # Subtracting each path's initial value preserves UCP convergence -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {Z : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem TendstoUCP.initialIncrement (hu : TendstoUCP P Z l Y) :
    TendstoUCP P (fun n t ω ↦ Z n t ω - Z n 0 ω) l
      (fun t ω ↦ Y t ω - Y 0 ω) := by
  have hs := hu.sub (hu.stoppedProcess (fun _ ↦ ⊥))
  simp only [stoppedProcess_const_bot] at hs
  exact hs

end ProbabilityTheory
