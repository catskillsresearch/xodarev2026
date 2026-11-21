/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Algebra

/-! # The source elementary integral as a genuine linear map

The submodule's carrier is exactly the existing source predicate. No bounded-input
substitute, quotient or additional integrand class is introduced. The codomain here
is raw random variables; measurability and convergence in measure have separate APIs.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def simplePredictableSubmodule (F : Filtration ℝ≥0 mΩ) : Submodule ℝ (ℝ≥0 → Ω → ℝ) where
  carrier := {H | IsSimplePredictable H F}
  zero_mem' := IsSimplePredictable.zero F
  add_mem' := fun hH hK ↦ hH.add hK
  smul_mem' := fun c _ hH ↦ hH.smul c

@[simp] theorem mem_simplePredictableSubmodule {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} : H ∈ simplePredictableSubmodule F ↔ IsSimplePredictable H F := Iff.rfl

noncomputable def elementaryIntegralLinearMap (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) : simplePredictableSubmodule F →ₗ[ℝ] (Ω → ℝ) where
  toFun := fun H ↦ H.property.elementaryIntegral X
  map_add' := fun H K ↦ H.property.elementaryIntegral_add K.property X
  map_smul' := fun c H ↦ H.property.elementaryIntegral_smul c X

@[simp] theorem elementaryIntegralLinearMap_apply (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) (H : simplePredictableSubmodule F) :
    elementaryIntegralLinearMap F X H = H.property.elementaryIntegral X := rfl

end ProbabilityTheory
