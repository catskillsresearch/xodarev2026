/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale.IntegrableVariation
public import StochLean.Probability.Process.Semimartingale.Quasimartingale.RaoLocal
public import StochLean.Probability.Process.FiniteVariation.TerminalLimit
public import StochLean.Probability.Process.LocalMartingale.Bounded

/-! # Predictable compensators of integrable-variation processes

An adapted cadlag process with integrable whole-half-line variation and an
integrable initial value is an actual quasimartingale. Rao's proved theorem
constructs its normalized predictable integrable-variation part. The local
martingale remainder has integrable variation as well, hence the actual
initial value plus actual total variation is an integrable common path
envelope. The existing dominated-local-martingale theorem upgrades it to a
true uniformly integrable martingale.

No compensator, terminal random variable, convergence certificate, or new
process selector is assumed. The original initial value remains in the
martingale, and the compensator mean is `E[X t] - E[X 0]`, not `E[X t]`.
Uniqueness permits an arbitrary predictable finite-variation competitor
whose initial value is zero only almost surely and whose remainder is only
a local martingale.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Every adapted cadlag integrable-variation process with integrable initial
value has a unique normalized predictable IV compensator, and its actual
remainder is a true UI martingale. The expectation identity retains the
arbitrary initial value. Uniqueness requires only predictable finite
variation and a local-martingale remainder from the competing part. -/
theorem HasIntegrableVariation.exists_unique_predictable_compensator
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasIntegrableVariation A P ∧ IsUIMartingale (X - A) F P ∧
      (∀ t, Integrable (A t) P ∧
        (∫ ω, A t ω ∂P) = (∫ ω, X t ω ∂P) - ∫ ω, X 0 ω ∂P) ∧
      ∀ B : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F B → HasFiniteVariationPaths B P →
        B 0 =ᵐ[P] 0 → IsLocalMartingale (X - B) F P → Indistinguishable A B P := by
  have hq := hv.isQuasimartingale ha hc hi0
  obtain ⟨M, A, hM, hpA, hcA, hA0, hvA, _, heX, huniq⟩ :=
    hq.exists_unique_rao_decomposition hF
  have heM : M = X - A := eq_sub_of_add_eq heX.symm
  have hvM : HasIntegrableVariation M P := by
    rw [heM]
    exact hv.sub hvA ha hpA.stronglyAdapted.adapted hF hc (Eventually.of_forall hcA)
  have hM0 : M 0 = X 0 := by
    rw [heM]
    change X 0 - A 0 = X 0
    rw [hA0, sub_zero]
  have hiM0 : Integrable (M 0) P := by
    rw [hM0]
    exact hi0
  have hbound : ∀ᵐ ω ∂P, ∀ t,
      ‖M t ω‖ ≤ ‖M 0 ω‖ + (eVariationOn (M · ω) univ).toReal :=
    hvM.hasFiniteVariationPaths.ae_norm_le_initial_add_of_totalVariation_le
      hvM.ae_forall_totalVariationProcess_le
  have huM : IsUIMartingale M F P :=
    hM.isUIMartingale_of_integrable_envelope
      (hiM0.norm.add hvM.integrable_eVariationOn_toReal) hbound
  have hu : IsUIMartingale (X - A) F P := heM ▸ huM
  have hiA (t : ℝ≥0) : Integrable (A t) P := by
    have he : A t = X t - (X - A) t := by
      funext ω
      change A t ω = X t ω - (X t ω - A t ω)
      ring
    rw [he]
    exact (hq.integrable t).sub (hu.1.integrable t)
  refine ⟨A, hpA, hcA, hA0, hvA, hu, ?_, ?_⟩
  · intro t
    refine ⟨hiA t, ?_⟩
    have hmean := huM.1.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ t)
      (@MeasurableSet.univ Ω (F 0))
    rw [setIntegral_univ, setIntegral_univ] at hmean
    change (∫ ω, M 0 ω ∂P) = ∫ ω, M t ω ∂P at hmean
    rw [hM0, heM] at hmean
    change (∫ ω, X 0 ω ∂P) = ∫ ω, X t ω - A t ω ∂P at hmean
    rw [integral_sub (hq.integrable t) (hiA t)] at hmean
    linarith only [hmean]
  · intro B hpB hvB hB0 hNB
    have heB : Indistinguishable X ((X - B) + B) P := by
      filter_upwards with ω t
      change X t ω = (X t ω - B t ω) + B t ω
      ring
    exact (huniq (X - B) B hNB hpB hvB hB0 heB).2

end ProbabilityTheory
