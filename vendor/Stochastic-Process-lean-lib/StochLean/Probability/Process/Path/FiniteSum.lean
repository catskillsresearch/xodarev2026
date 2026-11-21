/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Step

/-! # Finite sums on one common path event

The ambient family need not be countable. Only the selected finite set of
path events is intersected, and the empty sum is the continuous zero path.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem HasCagladPaths.finset_sum (S : Finset ι) {X : ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i ∈ S, HasCagladPaths (X i) P) :
    HasCagladPaths (fun t ω ↦ ∑ i ∈ S, X i t ω) P := by
  filter_upwards [(eventually_all_finset S).2 hX] with ω hω
  exact IsCagladPath.finset_sum S (fun i t ↦ X i t ω) hω

end ProbabilityTheory
