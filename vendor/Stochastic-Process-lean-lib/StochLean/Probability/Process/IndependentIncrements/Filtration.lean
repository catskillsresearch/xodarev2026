/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Independence.OrderedPast
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Process.Adapted

/-! # Filtration-independent increments imply independent increments

The finite-family conclusion uses independence from the entire past
sigma-algebra, not merely pairwise independent increments.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

theorem _root_.MeasureTheory.Adapted.hasIndepIncrements_of_indep_comap
    {T Ω E : Type*} [Preorder T] {mΩ : MeasurableSpace Ω}
    [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration T mΩ}
    {X : T → Ω → E} (hX : Adapted F X)
    (hind : ∀ s t, s ≤ t →
      Indep (F s) (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P) :
    HasIndepIncrements X P := by
  intro n t ht
  apply (iIndepFun_iff_iIndep _ _ _).2
  apply iIndep_of_indep_previous (n := fun i : Fin n ↦ F (t i.castSucc))
  · intro i j hij
    apply Measurable.comap_le
    exact ((hX (t i.succ)).mono (F.mono (ht (by
      change i.val + 1 ≤ j.val
      exact hij))) le_rfl).sub
      ((hX (t i.castSucc)).mono (F.mono (ht (by
        change i.val ≤ j.val
        exact le_of_lt hij))) le_rfl)
  · intro i
    exact hind _ _ (ht (by change i.val ≤ i.val + 1; omega))

end ProbabilityTheory
