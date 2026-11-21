/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicContinuous
public import StochLean.Probability.Martingale.Doob.DyadicLimitClosing
public import StochLean.Probability.Process.Measurability.Predictable

/-! # Continuous Doob decomposition of a bounded supermartingale

The actual dyadic increasing parts have a continuous increasing UCP limit.
Their terminal L2 limit closes the sum with the original supermartingale.
Consequently the sum is a genuine uniformly integrable cadlag martingale,
not merely a process declared to be one in a decomposition certificate.

The proof accepts a genuine global conditional modulus with proved convergence.
The original bounded, totally-inaccessible-positive-jump interface constructs that
modulus internally. Other source conditions can use the same dyadic construction.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ}

/-- An actual continuous predictable increasing compensator and an actual
L2 closing variable are constructed from the bounded supermartingale and
a genuine convergent global conditional modulus.
The initial value of `X` need not be zero; the increasing part starts at zero. -/
theorem Supermartingale.exists_continuous_doob_decomposition_of_bound_of_globalConditionalModulus
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    (hGM : TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)))
    (hG2 : ∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P)
    (hGE : Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0)) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      MemLp L 2 P ∧ (∀ t, X t + A t =ᵐ[P] P[L | F t]) ∧
      Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧
      (∀ t, MemLp (A t) 2 P ∧ MemLp (X t + A t) 2 P) ∧
      TendstoUCP P (dyadicDoobStep X F P) atTop A := by
  obtain ⟨A, hAa, hAc, hA0, hAm, hAv, hBA⟩ :=
    hX.exists_continuous_dyadicDoob_limit_of_globalConditionalModulus
      hF hc hN hbound hG hGM hG2 hGE
  obtain ⟨U, V, hU, _, hlU, hV, hUV⟩ :=
    hX.exists_dyadicDoob_terminal_L2_limit_of_globalConditionalModulus hc hN hbound hG hG2 hGE
  obtain ⟨Z, _, hZ, _, hlZ⟩ := hX.exists_bounded_actualLimit hc hbound
  obtain ⟨hclose, hM, hUI, hL2⟩ := hX.dyadic_ucpLimit_martingale_closing hc
    (fun t ↦ hbound.mono fun _ hω ↦ hω t) hZ hU hV hlZ hlU hUV hAa hBA
  have hAp : IsStronglyPredictable F A :=
    hAa.isStronglyPredictable_of_leftContinuous (fun ω t ↦ (hAc ω).continuousWithinAt)
  have hAcad : HasCadlagPaths A P :=
    Eventually.of_forall fun ω ↦ IsContinuousPath.isCadlagPath (hAc ω)
  exact ⟨A, Z + V, hAa, hAp, hAc, hA0, hAm, hAv, hZ.add hV, hclose,
    hM, hc.add hAcad, hUI, hL2, hBA⟩

/-- Bounded TI-jump source existence, with its original public interface. -/
theorem Supermartingale.exists_continuous_doob_decomposition_of_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      MemLp L 2 P ∧ (∀ t, X t + A t =ᵐ[P] P[L | F t]) ∧
      Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧
      (∀ t, MemLp (A t) 2 P ∧ MemLp (X t + A t) 2 P) ∧
      TendstoUCP P (dyadicDoobStep X F P) atTop A := by
  obtain ⟨G, hG, hGM, hG2, hGE, _⟩ :=
    hX.exists_globalConditionalModulus_L2_convergence_of_bound hF hc hJ hN hbound
  exact hX.exists_continuous_doob_decomposition_of_bound_of_globalConditionalModulus
    hF hc hN hbound hG hGM hG2 hGE

end MeasureTheory
