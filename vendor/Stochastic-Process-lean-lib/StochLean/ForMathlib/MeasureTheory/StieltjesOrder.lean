/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes

/-! # Ordering half-line Stieltjes measures by their increments

The difference of the two distribution functions is itself a Stieltjes
function, so additivity of Mathlib's existing measure construction suffices.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace StochLean

theorem stieltjesMeasure_le_of_increment_le (f g : StieltjesFunction ℝ≥0)
    (h : ∀ s t, s ≤ t → f t - f s ≤ g t - g s) : f.measure ≤ g.measure := by
  let d : StieltjesFunction ℝ≥0 :=
    ⟨fun t ↦ g t - f t, fun s t hst ↦ by linarith only [h s t hst],
      fun t ↦ (g.right_continuous t).sub (f.right_continuous t)⟩
  have heq : g = f + d := by
    apply StieltjesFunction.ext
    intro t
    change g t = f t + (g t - f t)
    ring
  rw [heq, StieltjesFunction.measure_add]
  exact Measure.le_add_right le_rfl

end StochLean
