/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.TerminalMoments
public import StochLean.Probability.Martingale.Convergence.ContinuousL2Closure

/-! # L2 closing variables and the terminal raw energy identity

Finite expected terminal raw energy constructs an actual L2 closing variable
with integer-time almost-sure and L2 convergence. The finite-time moment
identity and monotone convergence identify its second moment with terminal
raw energy. Whole-half-line convergence remains a separate assertion.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.exists_memLp_two_closing_terminal_energy
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hI : (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) < ∞) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 2 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) ∧
      ENNReal.ofReal (∫ ω, Z ω ^ 2 ∂P) = (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P) ∧
      (∫ ω, Z ω ^ 2 ∂P) = (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P).toReal := by
  have hL := hX.squareIntegrable_of_integrable_quadraticVariationInfinity hF hM hI
  obtain ⟨Z, hZ, hlim, hLp, hclose, hE, _⟩ :=
    hL.1.exists_memLp_two_closing_and_second_moment_limit
      hX.hasCadlagPaths.hasRightContinuousPaths hL.2
      (hX.second_moment_le_integral_quadraticVariationInfinity hF hM hI)
  let a (n : ℕ) := ∫⁻ ω, ENNReal.ofReal (hX.quadraticVariation hF (n : ℝ≥0) ω) ∂P
  have ha : Monotone a := by
    intro i j hij
    apply lintegral_mono_ae
    filter_upwards [hX.hasMonotonePaths_quadraticVariation hF] with ω hω
    exact ENNReal.ofReal_le_ofReal (hω (by exact_mod_cast hij))
  have hA : Tendsto a atTop (𝓝 (∫⁻ ω, hX.quadraticVariationInfinity hF ω ∂P)) := by
    rw [hX.lintegral_quadraticVariationInfinity_eq_iSup hF]
    exact tendsto_atTop_iSup ha
  have he (n : ℕ) : ENNReal.ofReal (∫ ω, X (n : ℝ≥0) ω ^ 2 ∂P) = a n := by
    rw [← (hX.integrable_quadraticVariation_and_integral_eq hF hL _).2]
    apply ofReal_integral_eq_lintegral_ofReal
      (hX.integrable_quadraticVariation_and_integral_eq hF hL _).1
    exact (hX.initial_sq_le_quadraticVariation hF).mono
      fun ω hω ↦ (sq_nonneg _).trans (hω _)
  have hAZ : Tendsto a atTop (𝓝 (ENNReal.ofReal (∫ ω, Z ω ^ 2 ∂P))) := by
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hE).congr'
      (Eventually.of_forall he)
  have hEq := tendsto_nhds_unique hAZ hA
  refine ⟨Z, hZ, hlim, hLp, hclose, hEq, ?_⟩
  rw [← hEq, ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]

end ProbabilityTheory
