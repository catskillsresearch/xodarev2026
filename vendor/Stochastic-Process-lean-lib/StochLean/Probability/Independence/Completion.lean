/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Augmentation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw

/-! # Laws and independence under genuine measure completion

Adjoining all ambient null sets adds only almost-sure versions of old events.
Their probabilities and independence are unchanged. The measure and ambient
space are actually completed; completeness of the old ambient space is not
assumed or asserted.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace ProbabilityTheory

variable {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {P : Measure Ω}

instance _root_.MeasureTheory.Measure.isProbabilityMeasure_completion [IsProbabilityMeasure P] :
    IsProbabilityMeasure P.completion := ⟨by change P univ = 1; exact measure_univ⟩

theorem exists_measurable_ae_eq_of_sup_nullSets {A : Set Ω}
    (hA : MeasurableSet[m₁ ⊔ Filtration.nullSets P] A) :
    ∃ B : Set Ω, MeasurableSet[m₁] B ∧ A =ᵐ[P] B := by
  have hle : m₁ ⊔ Filtration.nullSets P ≤ eventuallyMeasurableSpace m₁ (ae P) := by
    refine sup_le le_eventuallyMeasurableSpace ?_
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact ⟨∅, @MeasurableSet.empty Ω m₁, ae_eq_empty.mpr hs⟩
  exact hle A hA

theorem Indep.sup_nullSets_left (hi : Indep m₁ m₂ P) :
    Indep (m₁ ⊔ Filtration.nullSets P) m₂ P := by
  apply (Indep_iff _ _ _).mpr
  intro A B hA hB
  obtain ⟨C, hC, hAC⟩ := exists_measurable_ae_eq_of_sup_nullSets hA
  have hab : (A ∩ B : Set Ω) =ᵐ[P] (C ∩ B : Set Ω) := hAC.inter (EventuallyEq.refl _ _)
  rw [measure_congr hab, measure_congr hAC]
  exact (Indep_iff _ _ _).mp hi C B hC hB

theorem Indep.sup_nullSets_right (hi : Indep m₁ m₂ P) :
    Indep m₁ (m₂ ⊔ Filtration.nullSets P) P := hi.symm.sup_nullSets_left.symm

theorem Indep.completion (hi : Indep m₁ m₂ P) :
    @Indep (NullMeasurableSpace Ω P) m₁ m₂ inferInstance P.completion := by
  apply (Indep_iff _ _ _).mpr
  intro A B hA hB
  change P (A ∩ B) = P A * P B
  exact (Indep_iff _ _ _).mp hi A B hA hB

theorem HasLaw.completion {E : Type*} [MeasurableSpace E] {Y : Ω → E} {ν : Measure E}
    (hY : HasLaw Y ν P) : HasLaw (fun ω : NullMeasurableSpace Ω P ↦ Y ω) ν P.completion := by
  have hm : Measurable (fun ω : NullMeasurableSpace Ω P ↦ Y ω) := hY.aemeasurable.nullMeasurable
  refine ⟨hm.aemeasurable, ?_⟩
  rw [← hY.map_eq]
  ext A hA
  rw [Measure.map_apply hm hA, Measure.map_apply_of_aemeasurable hY.aemeasurable hA]
  rfl

end ProbabilityTheory
