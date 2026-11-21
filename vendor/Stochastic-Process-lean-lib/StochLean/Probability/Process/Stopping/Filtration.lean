/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Finite

/-! # Stopping-time witnesses under filtration enlargement -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F G : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem IsStoppingTime.monoFiltration (hτ : IsStoppingTime F τ) (hFG : ∀ t, F t ≤ G t) :
    IsStoppingTime G τ := fun t ↦ hFG t _ (hτ t)

theorem IsStoppingTime.measurableSpace_monoFiltration (hτ : IsStoppingTime F τ)
    (hFG : ∀ t, F t ≤ G t) : hτ.measurableSpace ≤ (hτ.monoFiltration hFG).measurableSpace := by
  intro s hs
  exact ⟨(iSup_mono hFG) s hs.1, fun t ↦ hFG t _ (hs.2 t)⟩

end MeasureTheory

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F G : Filtration ℝ≥0 mΩ}

def mapFiltration (τ : FiniteStoppingTime F) (hFG : ∀ t, F t ≤ G t) : FiniteStoppingTime G :=
  ⟨τ.toFun, τ.isStoppingTime.monoFiltration hFG⟩

@[simp] theorem mapFiltration_apply (τ : FiniteStoppingTime F) (hFG : ∀ t, F t ≤ G t) (ω : Ω) :
    τ.mapFiltration hFG ω = τ ω := rfl

theorem measurableSpace_le_mapFiltration (τ : FiniteStoppingTime F) (hFG : ∀ t, F t ≤ G t) :
    τ.measurableSpace ≤ (τ.mapFiltration hFG).measurableSpace :=
  τ.isStoppingTime.measurableSpace_monoFiltration hFG

end ProbabilityTheory.FiniteStoppingTime
