/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableLocal
public import StochLean.Probability.Martingale.Convergence.ContinuousMonotoneL1
public import StochLean.Probability.Process.FiniteVariation.MonotoneIntegrable

/-! # Integrable terminal compensators under a lower expectation bound

The actual general local Doob--Meyer construction gives finite-time compensator
integrability and an expectation bound by the source's loss of mean. A signed
lower bound on that mean makes these compensator means uniformly bounded.
The existing monotone terminal theorem constructs the same compensator's actual
integrable terminal variable, common path envelope, and whole-half-line L1 limit.
The actual variation owner is then globally integrable by its envelope theorem.

The finite-limit formulation of Protter III.16 follows from antitonicity of
supermartingale expectations. No terminal variable, compensator, convergence
certificate, Class D hypothesis, or additional selector is supplied as input.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A lower bound on the source expectations constructs an actual integrable
terminal compensator with global integrable variation. The bound may be signed;
the arbitrary initial value remains in the compensated local martingale. -/
theorem Supermartingale.exists_predictable_doob_integrable_terminal_of_integral_bounded_below
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {C : ℝ} (hb : ∀ t, C ≤ ∫ ω, X t ω ∂P) :
    ∃ A : ℝ≥0 → Ω → ℝ, ∃ Z : Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      HasIntegrableVariation A P ∧ IsLocalMartingale (X + A) F P ∧
      (∀ t, Integrable (A t) P ∧
        (∫ ω, A t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - ∫ ω, X t ω ∂P) ∧
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - C ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      UniformIntegrable A 1 P ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  obtain ⟨A, hp, hca, h0, hm, hlv, hM, hmean⟩ :=
    hX.exists_predictable_doob_local_decomposition hF hc
  have ha : Adapted F A := hp.stronglyAdapted.adapted
  have hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω := by
    filter_upwards [hm] with ω hω t
    have hz : A 0 ω = 0 := congrFun h0 ω
    have h : A 0 ω ≤ A t ω := hω (bot_le : (0 : ℝ≥0) ≤ t)
    rwa [hz] at h
  have hbound (t : ℝ≥0) : (∫ ω, A t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - C :=
    (hmean t).2.trans (sub_le_sub_left (hb t) _)
  obtain ⟨Z, hiZ, hEZ, hAZ, hlim, hui, hL1⟩ :=
    hm.exists_integrable_terminal_of_integral_bounded ha (fun t ↦ (hmean t).1) hn hbound
  have hv : HasIntegrableVariation A P :=
    (hm.hasIntegrableVariation_of_integrable_bound ha hF (Eventually.of_forall hca)
      (Eventually.of_forall fun ω ↦ congrFun h0 ω) hiZ hAZ).1
  exact ⟨A, Z, hp, hca, h0, hm, hlv, hv, hM, hmean, hiZ, hEZ, hAZ, hlim, hui, hL1⟩

/-- The finite-limit supplement in Protter III.16. A finite limiting source
mean is a lower bound at every time, by the actual supermartingale inequality. -/
theorem Supermartingale.exists_predictable_doob_integrable_terminal_of_tendsto_integral
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {l : ℝ} (hl : Tendsto (fun t : ℝ≥0 ↦ ∫ ω, X t ω ∂P) atTop (𝓝 l)) :
    ∃ A : ℝ≥0 → Ω → ℝ, ∃ Z : Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      HasIntegrableVariation A P ∧ IsLocalMartingale (X + A) F P ∧
      (∀ t, Integrable (A t) P ∧
        (∫ ω, A t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - ∫ ω, X t ω ∂P) ∧
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - l ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      UniformIntegrable A 1 P ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  have hm : Antitone (fun t ↦ ∫ ω, X t ω ∂P) := by
    intro s t hst
    simpa only [setIntegral_univ] using
      hX.setIntegral_le hst (@MeasurableSet.univ Ω (F s))
  exact hX.exists_predictable_doob_integrable_terminal_of_integral_bounded_below hF hc
    (fun t ↦ hm.le_of_tendsto hl t)

end MeasureTheory
