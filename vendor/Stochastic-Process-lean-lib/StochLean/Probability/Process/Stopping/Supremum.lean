/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-! # Countable suprema of nonnegative stopping times

The closed sublevel event is a countable intersection. Unlike infima, this
closure does not require right continuity of the filtration.
-/

@[expose] public section

open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

protected theorem finset_sup_nnreal {ι : Type*} (s : Finset ι)
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i ∈ s, IsStoppingTime F (τ i)) :
    IsStoppingTime F (fun ω ↦ s.sup (fun i ↦ τ i ω)) := by
  intro t
  have he : {ω | s.sup (fun i ↦ τ i ω) ≤ (t : WithTop ℝ≥0)} =
      ⋂ i ∈ s, {ω | τ i ω ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sup_le_iff, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.biInter s.countable_toSet fun i hi ↦ hτ i hi t

protected theorem iSup_nnreal {ι : Type*} [Countable ι] {τ : ι → Ω → WithTop ℝ≥0}
    (hτ : ∀ i, IsStoppingTime F (τ i)) : IsStoppingTime F (fun ω ↦ ⨆ i, τ i ω) := by
  intro t
  have he : {ω | (⨆ i, τ i ω) ≤ (t : WithTop ℝ≥0)} = ⋂ i, {ω | τ i ω ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, iSup_le_iff, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter fun i ↦ hτ i t

end MeasureTheory.IsStoppingTime
