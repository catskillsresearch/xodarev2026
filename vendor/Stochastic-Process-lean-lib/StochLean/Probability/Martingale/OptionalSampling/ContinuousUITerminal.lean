/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousL1Limit
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousInfiniteTerminal

/-! # Constructed UI terminal values and possibly infinite optional sampling

Uniform integrability and right continuity construct the actual terminal
variable and its full-time AE/L1 limits. The terminal sampling theorem then
applies to arbitrary, possibly infinite, stopping times. The caller supplies
neither a terminal limit nor any square-integrability premise.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem exists_terminal_optionalSampling_of_uniformIntegrable
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P)
    (hu : UniformIntegrable X 1 P) (hF : F.IsUsual P) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 1 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) ∧
      (∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ),
        Integrable (stoppedValueWithTerminal X Z τ) P ∧
        stoppedValueWithTerminal X Z τ =ᵐ[P] P[Z | hτ.measurableSpace]) ∧
      (∀ (σ τ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime F σ) (_hτ : IsStoppingTime F τ),
        (∀ᵐ ω ∂P, σ ω ≤ τ ω) →
        stoppedValueWithTerminal X Z σ =ᵐ[P]
          P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace]) := by
  obtain ⟨Z, hZ, hlim, hL1, hclose⟩ := hX.exists_integrable_limit_of_uniformIntegrable hc hu
  refine ⟨Z, hZ, hlim, hL1, hclose, ?_, ?_⟩
  · intro τ hτ
    exact ⟨hX.integrable_stoppedValueWithTerminal hu hF hc hlim hτ,
      hX.stoppedValueWithTerminal_ae_eq_condExp_terminal hu hF hc hlim hτ⟩
  · intro σ τ hσ hτ hle
    exact hX.stoppedValueWithTerminal_ae_eq_condExp_of_ae_le hu hF hc hlim hσ hτ hle

end MeasureTheory.Martingale
