/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Independence.Completion
public import StochLean.Probability.Process.StationaryIncrements

/-! # Stationary increment laws under genuine completion

The original increment random variables keep their exact image laws on the
genuinely completed sample space. Consequently stationary increment laws are
preserved without selecting a new process version. No path regularity,
probability-measure assumption, or initial normalization is involved.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

/-- Genuine completion preserves every stationary increment identity of the
original process, with the original initial value and source measure. -/
theorem HasStationaryIncrements.completion (hX : HasStationaryIncrements X P) :
    HasStationaryIncrements
      (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω) P.completion := by
  intro s t
  have h := hX s t
  let Y : Ω → ℝ := fun ω ↦ X (s + t) ω - X s ω
  let Z : Ω → ℝ := fun ω ↦ X t ω - X 0 ω
  have hY : HasLaw Y (P.map Y) P := ⟨h.aemeasurable_fst, rfl⟩
  have hZ : HasLaw Z (P.map Y) P := h.hasLaw hY
  exact hY.completion.identDistrib hZ.completion

end ProbabilityTheory
