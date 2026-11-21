/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.TerminalClosure
public import StochLean.Probability.Martingale.Convergence.ContinuousL2Limit

/-! # Terminal convergence under finite expected raw energy

Protter II.27 Corollary 4 on the actual semimartingale domain: the constructed
L2 closing variable is the almost-sure and L2 limit along the entire half-line,
and its second moment equals expected terminal raw quadratic variation.
Continuous local martingales construct their semimartingale witness internally.
The general local-martingale-to-semimartingale bridge is still separate work.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.exists_memLp_two_limit_terminal_energy
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 2 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) ∧
      (∫ ω, Z ω ^ 2 ∂P) = (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P).toReal := by
  have hL := hX.squareIntegrable_of_integrable_quadraticVariationInfinity hF hM hI
  obtain ⟨Z, hZ, hna, hn, hclose, _, hE⟩ :=
    hX.exists_memLp_two_closing_terminal_energy hF hM hI
  exact ⟨Z, hZ, hL.1.ae_tendsto_of_integer_L2_closing
      hX.hasCadlagPaths.hasRightContinuousPaths hZ hclose hna hn,
    hL.1.tendsto_eLpNorm_two_of_integer_closing (hZ.integrable (by norm_num)) hclose hn,
    hclose, hE⟩

theorem IsContinuousLocalMartingale.exists_memLp_two_limit_terminal_energy
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hI : (∫⁻ ω, (hX.isSemimartingale hF).quadraticVariationInfinity hF ω ∂P) < ∞) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 2 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) ∧
      (∫ ω, Z ω ^ 2 ∂P) =
        (∫⁻ ω, (hX.isSemimartingale hF).quadraticVariationInfinity hF ω ∂P).toReal :=
  (hX.isSemimartingale hF).exists_memLp_two_limit_terminal_energy hF hX.1 hI

end ProbabilityTheory
