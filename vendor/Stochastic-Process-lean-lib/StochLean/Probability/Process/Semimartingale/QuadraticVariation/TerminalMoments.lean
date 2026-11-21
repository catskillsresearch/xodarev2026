/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Terminal
public import StochLean.Probability.Martingale.Inequalities.DoobGlobalL2

/-! # Terminal energy, global L2 boundedness and maximal envelopes

Finite expected terminal raw energy is equivalent to true martingality with
uniformly bounded second moments on the existing semimartingale domain.
The global Doob envelope is constructed, rather than assumed for a local
martingale. These results do not yet assert martingale terminal convergence.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.lintegral_quadraticVariationInfinity_le_of_bounded_second_moments
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hM : IsSquareIntegrableMartingale X F P) {C : ℝ}
    (hb : ∀ t, (∫ ω, X t ω ^ 2 ∂P) ≤ C) :
    (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) ≤ ENNReal.ofReal C := by
  rw [hX.lintegral_quadraticVariationInfinity_eq_iSup hF]
  apply iSup_le
  intro n
  have hn : 0 ≤ᵐ[P] hX.quadraticVariation hF (n : ℝ≥0) :=
    (hX.initial_sq_le_quadraticVariation hF).mono fun ω hω ↦ (sq_nonneg _).trans (hω _)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hX.integrable_quadraticVariation_and_integral_eq hF hM _).1 hn,
    (hX.integrable_quadraticVariation_and_integral_eq hF hM _).2]
  exact ENNReal.ofReal_le_ofReal (hb _)

/-- A genuine global L2 bound is equivalent to finite expected terminal raw
energy for local martingales in the existing bracket domain. -/
theorem IsSemimartingale.integrable_quadraticVariationInfinity_iff
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P) :
    (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞ ↔
      IsSquareIntegrableMartingale X F P ∧ ∃ C : ℝ, ∀ t, (∫ ω, X t ω ^ 2 ∂P) ≤ C := by
  constructor
  · intro hI
    exact ⟨hX.squareIntegrable_of_integrable_quadraticVariationInfinity hF hM hI,
      (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P).toReal,
      hX.second_moment_le_integral_quadraticVariationInfinity hF hM hI⟩
  · rintro ⟨hL, C, hb⟩
    exact (hX.lintegral_quadraticVariationInfinity_le_of_bounded_second_moments
      hF hL hb).trans_lt ENNReal.ofReal_lt_top

theorem IsSemimartingale.exists_memLp_two_globalEnvelope_of_integrable_terminal_energy
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 4 * (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P).toReal := by
  have hL := hX.squareIntegrable_of_integrable_quadraticVariationInfinity hF hM hI
  apply hL.1.exists_memLp_two_globalEnvelope hX.hasCadlagPaths.hasRightContinuousPaths hL.2
  intro t
  simpa only [Real.norm_eq_abs, sq_abs] using
    hX.second_moment_le_integral_quadraticVariationInfinity hF hM hI t

end ProbabilityTheory
