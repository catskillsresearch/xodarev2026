/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.ActualNaturalPredictableExpectation
public import StochLean.Probability.Process.FiniteVariation.NaturalMartingale

/-! # Predictable integrable-variation processes are natural

Protter III.14 follows from the proved expectation identity for the actual
mixed bracket and its actual integrable terminal constructed from integrable
variation. Whole-halfline L1 convergence transfers zero fixed-time means to
that terminal. No candidate bracket martingale, terminal, or jump enumeration
is an input. The raw initial product is removed only by the explicit zero
initial-value hypothesis.

The existing martingale consequence of naturality also yields Yoeurp's lemma
for a bounded cadlag test martingale and this integrable-variation input. No
general local-martingale or locally-integrable-variation extension is asserted.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

/-- Protter III.14: a zero-initial predictable cadlag process of integrable
variation is natural for the existing raw bracket and its actual terminal. -/
theorem IsStronglyPredictable.isNatural_of_integrableVariation
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P) (hcA : HasCadlagPaths A P)
    (hv : HasIntegrableVariation A P) (h0 : A 0 =ᵐ[P] 0) : IsNatural A F P hF := by
  refine ⟨hA.stronglyAdapted.adapted, hcA, hv, h0, ?_⟩
  intro M hM hcM C hC hb
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let hSA := hv.hasFiniteVariationPaths.isSemimartingale hA.stronglyAdapted.adapted hF hcA
  have hiZero : Integrable (0 : Ω → ℝ) P :=
    ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩
  have hi0 : Integrable (A 0) P := hiZero.congr h0.symm
  obtain ⟨Z, hiZ, hlim, hL1, _⟩ :=
    hSM.exists_integrable_terminal_quadraticCovariation_of_right hSA hF hv hi0 hC hb
  have htest (t : ℝ≥0) :=
    hA.integrable_quadraticCovariation_and_integral_eq_zero_of_integrableVariation
      hF hcA hv h0 hM hcM C hC hb t
  refine ⟨Z, hiZ, hlim, ?_⟩
  have hmean := tendsto_integral_of_L1' Z hiZ.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ (htest t).1) hL1
  apply tendsto_nhds_unique hmean
  simpa only [fun t ↦ (htest t).2] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 ↦ (0 : ℝ)) atTop (𝓝 0))

/-- Yoeurp's bounded-test integrable-variation conclusion: the actual mixed
bracket is a UI martingale, derived from the proved naturality theorem. -/
theorem IsStronglyPredictable.isUIMartingale_quadraticCovariation_of_integrableVariation
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P) (hcA : HasCadlagPaths A P)
    (hv : HasIntegrableVariation A P) (h0 : A 0 =ᵐ[P] 0)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    IsUIMartingale
      ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
        (hv.hasFiniteVariationPaths.isSemimartingale hA.stronglyAdapted.adapted hF hcA) hF) F P :=
  (hA.isNatural_of_integrableVariation hF hcA hv h0).isUIMartingale_quadraticCovariation
    hM hcM C hC hb

end MeasureTheory
