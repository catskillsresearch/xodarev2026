/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableAlgebra

/-! # Real scaling of locally integrable variation

The actual unmasked stopped-variation criterion and the existing global
scaling theorem preserve local IV with exactly the same localizers. This
requires neither process adaptedness nor an initial moment. The zero scalar
is included; the variation criterion already justifies the unmasked form.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem HasLocallyIntegrableVariation.const_mul
    (hX : HasLocallyIntegrableVariation X F P) (c : ℝ) :
    HasLocallyIntegrableVariation (fun t ω ↦ c * X t ω) F P := by
  obtain ⟨τ, hτ, hv⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hX
  exact hasLocallyIntegrableVariation_iff_exists_stopped.mpr
    ⟨τ, hτ, fun n ↦ (hv n).const_mul c⟩

theorem HasLocallyIntegrableVariation.smul
    (hX : HasLocallyIntegrableVariation X F P) (c : ℝ) :
    HasLocallyIntegrableVariation (c • X) F P := by
  change HasLocallyIntegrableVariation (fun t ω ↦ c * X t ω) F P
  exact hX.const_mul c

end ProbabilityTheory
