/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Complex
public import StochLean.Probability.Process.LocalMartingale.Stability

/-! # Ordinary stopping of complex local martingales

The two existing real local-martingale predicates retain their Protter masks.
This is ordinary stopping of the process, not a replacement localization rule.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsComplexLocalMartingale.stoppedProcess
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ}
    (hZ : IsComplexLocalMartingale Z F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsComplexLocalMartingale (MeasureTheory.stoppedProcess Z τ) F P :=
  ⟨hZ.1.stoppedProcess hF hτ, hZ.2.stoppedProcess hF hτ⟩

end ProbabilityTheory
