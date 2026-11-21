/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.JumpExitIntegrability

/-! # Integrable envelopes for actual positive stopped jumps

A common envelope for all positive-time jumps bounds the original sampled
jump at an almost surely positive lifetime. Infinite lifetimes use explicit
terminal zero. Usual completeness gives measurability of the original sampled
coefficient even when cadlag regularity holds only almost surely. The envelope
is assumed integrable, so no finite-measure hypothesis is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {G : Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- A common positive-time envelope controls the original zero-terminal
sampled jump. The envelope's nonnegativity at infinity follows from any
positive-time bound; it is not an extra assumption. -/
theorem ae_norm_stopped_jump_le_of_positive_time_bound
    (hb : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ G ω)
    (hp : ∀ᵐ ω ∂P, 0 < τ ω) :
    ∀ᵐ ω ∂P,
      ‖stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω‖ ≤ G ω := by
  filter_upwards [hb, hp] with ω hbω hpω
  cases ht : τ ω with
  | top =>
    rw [stoppedValueWithTerminal_jump_eq_zero_of_top ht, norm_zero]
    exact (norm_nonneg (jumpProcess X 1 ω)).trans (hbω 1 zero_lt_one)
  | coe t =>
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
    exact hbω t (WithTop.coe_lt_coe.mp (ht ▸ hpω))

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
  {G : Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- An integrable common positive-time envelope makes the actual sampled jump
integrable. Neither the ambient measure nor the lifetime must be finite. -/
theorem Adapted.integrable_stopped_jump_of_integrable_positive_time_bound
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hτ : IsStoppingTime F τ) (hp : ∀ᵐ ω ∂P, 0 < τ ω)
    (hiG : Integrable G P)
    (hb : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ G ω) :
    Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) P := by
  exact hiG.mono'
    ((ha.stronglyMeasurable_stopped_jump_of_usual hF hc hτ).mono
      hτ.measurableSpace_le).aestronglyMeasurable
    (ae_norm_stopped_jump_le_of_positive_time_bound hb hp)

end MeasureTheory
