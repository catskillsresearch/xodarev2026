/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Monotonicity of Radon--Nikodym densities under measure domination -/

@[expose] public section

open MeasureTheory

namespace StochLean

theorem rnDeriv_le_of_measure_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ ν ρ : Measure Ω} [SigmaFinite ρ] [Measure.HaveLebesgueDecomposition ν ρ]
    (hμν : μ ≤ ν) (hνρ : ν ≪ ρ) : μ.rnDeriv ρ ≤ᵐ[ρ] ν.rnDeriv ρ := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ρ)
  intro s hs _
  rw [Measure.setLIntegral_rnDeriv' hνρ hs]
  exact (Measure.setLIntegral_rnDeriv_le s).trans (hμν s)

end StochLean
