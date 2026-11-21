/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousBounded
public import StochLean.Probability.Martingale.Doob.RegularGlobalConditionalModulus

/-! # Continuous Doob decomposition of bounded regular supermartingales

Vanishing expected jumps at every positive predictable stopping time, including
possibly infinite lifetimes with an explicit zero terminal jump, constructs the
actual global conditional modulus and its convergence. The existing dyadic
terminal-energy, UCP-completeness, and martingale-closing proofs then construct
the continuous predictable increasing part. No TI jump hypothesis, compensator,
terminal variable, modulus, or convergence certificate is a source input.

The original initial value of the supermartingale is unrestricted. Only the
constructed increasing part is normalized to start exactly at zero.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ}

/-- Actual continuous predictable increasing Doob decomposition on the bounded
predictable-jump-mean regularity domain. Its sum is a true cadlag UI martingale. -/
theorem
    Supermartingale.exists_continuous_doob_decomposition_of_bound_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      MemLp L 2 P ∧ (∀ t, X t + A t =ᵐ[P] P[L | F t]) ∧
      Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧
      (∀ t, MemLp (A t) 2 P ∧ MemLp (X t + A t) 2 P) ∧
      TendstoUCP P (dyadicDoobStep X F P) atTop A := by
  obtain ⟨G, hG, hGM, hG2, hGE, _⟩ :=
    hX.exists_globalConditionalModulus_L2_convergence_of_predictable_jump_mean_zero
      hF hc hN hbound hreg
  exact hX.exists_continuous_doob_decomposition_of_bound_of_globalConditionalModulus
    hF hc hN hbound hG hGM hG2 hGE

end MeasureTheory
