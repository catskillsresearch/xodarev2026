/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.Algebra

/-! # Finite sums in the existing real UCP topology -/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal

namespace ProbabilityTheory

theorem TendstoUCP.sum {Ω α κ : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {l : Filter α} (s : Finset κ)
    {X : κ → α → ℝ≥0 → Ω → ℝ} {Y : κ → ℝ≥0 → Ω → ℝ}
    (h : ∀ k ∈ s, TendstoUCP P (X k) l (Y k)) :
    TendstoUCP P (fun n ↦ ∑ k ∈ s, X k n) l (∑ k ∈ s, Y k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [sum_empty] using tendstoUCP_const l (0 : ℝ≥0 → Ω → ℝ)
  | @insert k s hk ih =>
    simp only [sum_insert hk]
    exact (h k (mem_insert_self _ _)).add (ih (fun j hj ↦ h j (mem_insert_of_mem hj)))

end ProbabilityTheory
