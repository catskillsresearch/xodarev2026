/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Independence.Completion
public import StochLean.Probability.Process.Filtration.IndependentIncrementsRightCont

/-! # Adaptation and future increments in the usual augmentation

Null-set enlargement takes place on the genuinely completed probability
space, followed by right continuation. No arbitrary information enlargement
is allowed by these theorems.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

theorem Adapted.withNullSets (ha : Adapted F X) (P : Measure Ω) :
    Adapted (F.withNullSets P) (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω) := by
  intro t
  exact (ha t).mono le_sup_left le_rfl

theorem Adapted.usualAugmentation (ha : Adapted F X) (P : Measure Ω) :
    Adapted (F.usualAugmentation P) (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω) := by
  intro t
  exact (ha t).mono (F.le_usualAugmentation P t) le_rfl

end MeasureTheory

namespace ProbabilityTheory

theorem HasRightContinuousPaths.indep_increment_usualAugmentation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hr : HasRightContinuousPaths X P) (ha : Adapted F X)
    (hi : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (F.usualAugmentation P s)
      (MeasurableSpace.comap (fun ω : NullMeasurableSpace Ω P ↦ X t ω - X s ω)
        inferInstance) P.completion := by
  have hr' : HasRightContinuousPaths
      (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω) P.completion := hr
  exact hr'.indep_increment_rightCont (ha.withNullSets P)
    (fun u v huv ↦ (hi u v huv).sup_nullSets_left.completion) hst

end ProbabilityTheory
