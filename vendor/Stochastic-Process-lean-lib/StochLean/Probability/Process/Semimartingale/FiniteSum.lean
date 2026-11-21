/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Stability

/-! # Finite sums of good-integrator semimartingales -/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.finset_sum {Ω κ : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : κ → ℝ≥0 → Ω → ℝ} (s : Finset κ)
    (hX : ∀ i ∈ s, IsSemimartingale (X i) F P) :
    IsSemimartingale (∑ i ∈ s, X i) F P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [sum_empty, Pi.zero_def] using
      (isSemimartingale_const_initial (F := F) (P := P)
        (Z := fun _ ↦ (0 : ℝ)) measurable_const)
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact (hX i (mem_insert_self _ _)).add
      (ih (fun j hj ↦ hX j (mem_insert_of_mem hj)))

/-- A fully indexed-family convenience form of the existing finite-sum theorem. -/
theorem isSemimartingale_finset_sum
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ι → ℝ≥0 → Ω → ℝ}
    (S : Finset ι) (hX : ∀ i, IsSemimartingale (X i) F P) :
    IsSemimartingale (∑ i ∈ S, X i) F P :=
  IsSemimartingale.finset_sum S (fun i _ ↦ hX i)

end ProbabilityTheory
