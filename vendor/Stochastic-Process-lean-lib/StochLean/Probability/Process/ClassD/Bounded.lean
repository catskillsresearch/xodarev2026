/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Stopping
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedIntegrability

/-! # Class D for bounded right-continuous supermartingales

A single bound on the original process controls the family of all bounded
stopping values. The existing truncation equivalence gives Class D for all
finite stopping times. No restriction to deterministic-time UI is substituted.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A common process bound gives genuine stopping-family Class D. -/
theorem Supermartingale.isClassD_of_bound (hX : Supermartingale X F P)
    (hr : HasRightContinuousPaths X P) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ C) : IsClassD X F P := by
  apply isClassD_iff_uniformIntegrable_bounded.mpr
  have hu : UniformIntegrable
      (fun _ : {τ : FiniteStoppingTime F | ∃ T, ∀ ω, τ ω ≤ T} ↦ fun _ : Ω ↦ C) 1 P :=
    uniformIntegrable_const le_rfl (by simp) (memLp_const C)
  apply hu.mono_norm
  · intro τ
    obtain ⟨T, hT⟩ := τ.2
    exact (hX.integrable_finiteStoppingTime_value τ.1 hT hr).aestronglyMeasurable
  · intro τ
    filter_upwards [hb] with ω hω
    exact (hω (τ.1 ω)).trans (le_abs_self C)

end MeasureTheory
