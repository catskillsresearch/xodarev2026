/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrableVariation
public import StochLean.Probability.Process.Semimartingale.L2Martingale

/-! # Natural finite-variation processes

Protter's naturality condition tests every actual bounded cadlag martingale
against the existing raw quadratic covariation. Each test requires an actual
integrable terminal limit with zero mean, so the condition cannot hold merely
because no terminal was supplied. No bracket or terminal selector is defined.

The usual-filtration proof is an explicit, proof-irrelevant parameter fixing
the working domain. It is not an extra process or bracket owner. Adaptedness,
cadlag paths, integrable variation, and the zero initial value are explicit
fields. In particular the raw bracket still has initial value `M 0 * A 0`;
its vanishing follows from the zero-initial field, not from renormalization.

Bounded test martingales obtain their semimartingale witnesses from actual
finite-time L2 integrability. Neither Yoeurp's lemma nor a martingale property
of the mixed bracket is assumed. Continuous IV processes give the elementary
naturality example through the already proved continuous-FV bracket identity.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- A common deterministic bound gives finite-time L2 integrability and hence
the existing source semimartingale property of a cadlag martingale. -/
theorem Martingale.isSemimartingale_of_bound (hM : Martingale M F P)
    (hF : F.IsUsual P) (hc : ProbabilityTheory.HasCadlagPaths M P) (C : ℝ)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    ProbabilityTheory.IsSemimartingale M F P := by
  apply hM.isSemimartingale_of_memLp hF hc
  intro t
  exact MemLp.of_bound (hM.integrable t).aestronglyMeasurable C
    (hb.mono fun _ hω ↦ hω t)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

/-- Natural processes test the actual raw bracket against every bounded
cadlag martingale. The terminal in each test is required to exist and to be
integrable; no martingale or predictable-bracket conclusion is an input. -/
structure IsNatural (A : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) [IsFiniteMeasure P] (hF : F.IsUsual P) : Prop where
  adapted : Adapted F A
  hasCadlagPaths : HasCadlagPaths A P
  hasIntegrableVariation : HasIntegrableVariation A P
  zero_ae : A 0 =ᵐ[P] 0
  exists_terminal_mean_zero : ∀ (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P)
    (hcM : HasCadlagPaths M P) (C : ℝ), 0 ≤ C →
    ∀ hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C,
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦
        (hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
          (hasIntegrableVariation.hasFiniteVariationPaths.isSemimartingale
            adapted hF hasCadlagPaths) hF t ω) atTop (𝓝 (Z ω))) ∧
      (∫ ω, Z ω ∂P) = 0

theorem IsNatural.isSemimartingale {hF : F.IsUsual P} (hA : IsNatural A F P hF) :
    IsSemimartingale A F P :=
  hA.hasIntegrableVariation.hasFiniteVariationPaths.isSemimartingale
    hA.adapted hF hA.hasCadlagPaths

/-- Any actual full-time terminal of a tested bracket is integrable and has
zero mean. Limit uniqueness identifies it with the witness in naturality;
neither its integrability nor equality to that witness is assumed. -/
theorem IsNatural.integrable_terminal_and_integral_eq_zero
    {hF : F.IsUsual P} (hA : IsNatural A F P hF)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) {Z : Ω → ℝ}
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦
      (hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
        hA.isSemimartingale hF t ω) atTop (𝓝 (Z ω))) :
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = 0 := by
  obtain ⟨W, hiW, hlW, heW⟩ := hA.exists_terminal_mean_zero M hM hcM C hC hb
  have he : W =ᵐ[P] Z := by
    filter_upwards [hlW, hlim] with ω hW hZ
    exact tendsto_nhds_unique hW hZ
  exact ⟨hiW.congr he, (integral_congr_ae he).symm.trans heW⟩

/-- Continuous IV processes with zero initial value are natural because
their actual mixed bracket is the raw initial product, which is zero here. -/
theorem HasIntegrableVariation.isNatural_of_continuous
    (hv : HasIntegrableVariation A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasContinuousPaths A P) (h0 : A 0 =ᵐ[P] 0) : IsNatural A F P hF := by
  refine ⟨ha, hc.hasCadlagPaths, hv, h0, ?_⟩
  intro M hM hcM C _hC hb
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let hSA := hv.hasFiniteVariationPaths.isSemimartingale ha hF hc.hasCadlagPaths
  have he := hSM.quadraticCovariation_initial_of_continuous_finiteVariation_right
    hSA hF hc hv.hasFiniteVariationPaths
  refine ⟨0, integrable_zero Ω ℝ P, ?_, by simp only [Pi.zero_apply, integral_zero]⟩
  filter_upwards [he, h0] with ω hω h0ω
  have hz : (fun t : ℝ≥0 ↦ hSM.quadraticCovariation hSA hF t ω) =
      fun _ ↦ (0 : ℝ) := by
    funext t
    rw [hω t, h0ω, Pi.zero_apply, mul_zero]
  change Tendsto (fun t : ℝ≥0 ↦ hSM.quadraticCovariation hSA hF t ω) atTop (𝓝 0)
  rw [hz]
  exact tendsto_const_nhds

/-- The zero process is natural for every usual finite-measure filtration. -/
theorem IsNatural.zero (hF : F.IsUsual P) : IsNatural (0 : ℝ≥0 → Ω → ℝ) F P hF :=
  hasIntegrableVariation_zero.isNatural_of_continuous
    (fun _ ↦ measurable_const) hF (ae_of_all _ fun _ ↦ continuous_const)
    (ae_of_all _ fun _ ↦ rfl)

end ProbabilityTheory
