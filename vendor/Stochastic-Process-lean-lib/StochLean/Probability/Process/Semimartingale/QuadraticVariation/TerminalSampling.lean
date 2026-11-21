/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.TerminalConvergence
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousInfiniteTerminal

/-! # Infinite-terminal sampling derived from finite expected raw energy

The actual L2 terminal variable, full-time limit and uniform integrability
are all constructed from the energy assumption. Every stopping time, finite
or infinite, has an L2 value using this terminal variable, with the expected
conditional-expectation and optional-sampling identities.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.exists_terminal_optionalSampling_of_finite_energy
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      (∫ ω, Z ω ^ 2 ∂P) = (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P).toReal ∧
      (∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ),
        MemLp (stoppedValueWithTerminal X Z τ) 2 P ∧
          stoppedValueWithTerminal X Z τ =ᵐ[P] P[Z | hτ.measurableSpace]) ∧
      ∀ (σ τ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime F σ) (_hτ : IsStoppingTime F τ),
        (∀ᵐ ω ∂P, σ ω ≤ τ ω) → stoppedValueWithTerminal X Z σ =ᵐ[P]
          P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace] := by
  have hL := hX.squareIntegrable_of_integrable_quadraticVariationInfinity hF hM hI
  obtain ⟨Z, hZ, hlim, _, hclose, hE⟩ := hX.exists_memLp_two_limit_terminal_energy hF hM hI
  have hu : UniformIntegrable X 1 P :=
    Martingale.uniformIntegrable_of_integrable_closing (hZ.integrable (by norm_num)) hclose
  have hr := hX.hasCadlagPaths.hasRightContinuousPaths
  refine ⟨Z, hZ, hlim, hE, ?_, ?_⟩
  · intro τ hτ
    exact ⟨hL.1.memLp_stoppedValueWithTerminal hu hF hr hlim hτ (by norm_num) hZ,
      hL.1.stoppedValueWithTerminal_ae_eq_condExp_terminal hu hF hr hlim hτ⟩
  · intro σ τ hσ hτ hle
    exact hL.1.stoppedValueWithTerminal_ae_eq_condExp_of_ae_le hu hF hr hlim hσ hτ hle

end ProbabilityTheory
