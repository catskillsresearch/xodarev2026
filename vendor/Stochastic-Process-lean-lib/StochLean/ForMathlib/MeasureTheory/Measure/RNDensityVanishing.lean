/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Vanishing infimum of actual Radon--Nikodym densities

If a countable family's total masses have infimum zero, then the pointwise
infimum of its native RN densities is zero almost everywhere under the
reference measure. The integral of the infimum is bounded by every actual
mass. Neither pointwise monotonicity of chosen RN versions nor absolute
continuity or finite total reference measure is required.
-/

@[expose] public section

open Set

namespace MeasureTheory.Measure

/-- Vanishing infimum of total masses forces the infimum of native
Radon--Nikodym densities to vanish on one reference-measure event. -/
theorem ae_iInf_rnDeriv_eq_zero_of_iInf_mass_eq_zero
    {α : Type*} [MeasurableSpace α] (μ : ℕ → Measure α) (ν : Measure α)
    (hzero : (⨅ n, μ n univ) = 0) :
    ∀ᵐ x ∂ν, (⨅ n, (μ n).rnDeriv ν x) = 0 := by
  have hm : Measurable (fun x ↦ ⨅ n, (μ n).rnDeriv ν x) :=
    Measurable.iInf fun n ↦ (μ n).measurable_rnDeriv ν
  apply (lintegral_eq_zero_iff hm).mp
  apply le_antisymm _ zero_le
  calc
    (∫⁻ x, ⨅ n, (μ n).rnDeriv ν x ∂ν) ≤
        ⨅ n, ∫⁻ x, (μ n).rnDeriv ν x ∂ν :=
      le_iInf_lintegral (fun n ↦ (μ n).rnDeriv ν)
    _ ≤ ⨅ n, μ n univ :=
      iInf_mono fun n ↦ Measure.lintegral_rnDeriv_le (μ := μ n) (ν := ν)
    _ = 0 := hzero

end MeasureTheory.Measure
