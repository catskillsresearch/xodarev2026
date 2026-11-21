/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Usual

/-! # Null-set invariance of stopping-time sigma-algebras

Completeness of the initial sigma-algebra is essential here. Equality of
stopping times almost everywhere does not by itself identify their uncompleted
stopping-time sigma-algebras.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {σ τ : Ω → WithTop ℝ≥0}

theorem IsStoppingTime.measurableSpace_congr_ae_of_usual
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hF : F.IsUsual P) (heq : σ =ᵐ[P] τ) :
    hσ.measurableSpace = hτ.measurableSpace := by
  have hle {α β : Ω → WithTop ℝ≥0} (hα : IsStoppingTime F α)
      (hβ : IsStoppingTime F β) (hab : α =ᵐ[P] β) :
      hα.measurableSpace ≤ hβ.measurableSpace := by
    intro s hs
    refine ⟨hs.1, fun t ↦ ?_⟩
    have hc : IsCompleteSubMeasurableSpace P (F t) := fun a ha ↦
      F.mono bot_le a (hF.complete_initial a ha)
    let : MeasurableSpace Ω := F t
    apply measurableSet_setOfPred.mpr
    apply hc.measurable_congr_ae (measurableSet_setOfPred.mp (hs.2 t))
    filter_upwards [hab] with ω hω
    exact congrArg (fun r ↦ ω ∈ s ∧ r ≤ (t : WithTop ℝ≥0)) hω
  exact le_antisymm (hle hσ hτ heq) (hle hτ hσ heq.symm)

end MeasureTheory
