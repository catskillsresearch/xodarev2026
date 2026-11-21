/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Natural
public import StochLean.Probability.Process.Filtration.Augmentation
public import StochLean.Probability.Process.Equivalence

/-! # Usual natural filtrations of indistinguishable processes

Indistinguishable coordinatewise strongly measurable processes need not
generate equal raw natural filtrations. After adjoining all ambient null
sets, however, their coordinate information agrees. Completeness transfers
coordinate measurability, and the actual natural-filtration generators give
both inclusions. Applying the same native right continuation then identifies
their genuine usual natural augmentations on the completed sample space.

No right continuity of the raw filtration or paths is assumed, and the
measure need not be finite. No new filtration or process version is selected.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped NNReal

namespace MeasureTheory.Filtration

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [TopologicalSpace E] [MetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → E}

private theorem natural_withNullSets_le_of_indistinguishable
    (hX : ∀ t, StronglyMeasurable (X t)) (hY : ∀ t, StronglyMeasurable (Y t))
    (hXY : ProbabilityTheory.Indistinguishable X Y P) :
    (natural X hX).withNullSets P ≤ (natural Y hY).withNullSets P := by
  intro t
  change natural X hX t ⊔ nullSets P ≤ natural Y hY t ⊔ nullSets P
  refine sup_le ?_ le_sup_right
  change (⨆ j ≤ t, MeasurableSpace.comap (X j) inferInstance) ≤
    natural Y hY t ⊔ nullSets P
  refine iSup₂_le fun j hjt ↦ ?_
  have hc : IsCompleteSubMeasurableSpace P (natural Y hY t ⊔ nullSets P) := by
    intro A hA
    exact (le_sup_right : nullSets P ≤ natural Y hY t ⊔ nullSets P) A
      (MeasurableSpace.measurableSet_generateFrom hA)
  have hYj : Measurable[natural Y hY t ⊔ nullSets P] (Y j) :=
    ((stronglyAdapted_natural hY).stronglyMeasurable_le hjt).measurable.mono
      le_sup_left le_rfl
  exact (hc.measurable_congr_ae hYj (hXY.mono fun _ hω ↦ (hω j).symm)).comap_le

/-- Indistinguishable processes have equal genuine usual natural
augmentations on the completed ambient space. This does not identify their
raw natural filtrations and requires no finiteness assumption on the measure. -/
theorem natural_usualAugmentation_eq_of_indistinguishable
    (hX : ∀ t, StronglyMeasurable (X t)) (hY : ∀ t, StronglyMeasurable (Y t))
    (hXY : ProbabilityTheory.Indistinguishable X Y P) :
    (natural X hX).usualAugmentation P = (natural Y hY).usualAugmentation P := by
  change ((natural X hX).withNullSets P).rightCont =
    ((natural Y hY).withNullSets P).rightCont
  apply congrArg Filtration.rightCont
  exact le_antisymm (natural_withNullSets_le_of_indistinguishable hX hY hXY)
    (natural_withNullSets_le_of_indistinguishable hY hX hXY.symm)

end MeasureTheory.Filtration
