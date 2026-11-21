/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Data.Finset.Max

/-! # Independence from all previous information

Independence of each coordinate from a sigma-algebra containing every earlier
coordinate implies mutual independence. The proof uses finite intersections
and removes the largest index; pairwise independence alone is not substituted.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

theorem iIndep_of_indep_previous
    {ι Ω : Type*} [LinearOrder ι] {m n : ι → MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hprev : ∀ i j, i < j → m i ≤ n j) (hind : ∀ i, Indep (n i) (m i) P) :
    iIndep m P := by
  classical
  apply (iIndep_iff _ _).2
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro f hf; simp
  | insert a S hlt ih =>
    intro f hf
    have ha : a ∉ S := fun ha ↦ (lt_irrefl a) (hlt a ha)
    have hfs : ∀ i ∈ S, MeasurableSet[m i] (f i) :=
      fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hp : MeasurableSet[n a] (⋂ i ∈ S, f i) :=
      Finset.measurableSet_biInter S fun i hi ↦ hprev i a (hlt i hi) _ (hfs i hi)
    simp only [Finset.mem_insert, Set.iInter_iInter_eq_or_left]
    rw [Finset.prod_insert ha,
      (Indep_iff _ _ _).1 (hind a).symm _ _ (hf a (Finset.mem_insert_self a S)) hp,
      ih hfs]

end ProbabilityTheory
