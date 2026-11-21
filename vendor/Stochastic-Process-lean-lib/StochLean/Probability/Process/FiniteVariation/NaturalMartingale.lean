/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousCharacterization
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OneSidedStopping

/-! # The martingale consequence of naturality

The actual raw bracket of a natural integrable-variation process with a
globally bounded càdlàg martingale is a uniformly integrable martingale.
Testing naturality with the stopped martingale gives zero expectation at
every stopping time, including infinity, and the existing expected-stopping
characterization then gives the martingale and uniform integrability.

At infinity we use the bracket's actual terminal variable. At finite stopping
times the one-sided stopping identity makes the tested bracket eventually
constant on each path. No totalized value at infinity, square-integrability
of the finite-variation process, or Yoeurp theorem is used. The bracket keeps
its raw initial product throughout.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

/-- Naturality determines the actual terminal-valued stopped bracket at an
arbitrary stopping time. The supplied terminal is an actual full-half-line
path limit, not an arbitrary closing variable. -/
theorem IsNatural.integrable_stoppedValueWithTerminal_quadraticCovariation_and_integral_eq_zero
    {hF : F.IsUsual P} (hA : IsNatural A F P hF)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) {Z : Ω → ℝ}
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦
      (hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
        hA.isSemimartingale hF t ω) atTop (𝓝 (Z ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Integrable (stoppedValueWithTerminal
      ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
        hA.isSemimartingale hF) Z τ) P ∧
      (∫ ω, stoppedValueWithTerminal
        ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
          hA.isSemimartingale hF) Z τ ω ∂P) = 0 := by
  have hMs : Martingale (stoppedProcess M τ) F P :=
    hM.stoppedProcess_of_usual hF hcM.hasRightContinuousPaths hτ
  have hcs : HasCadlagPaths (stoppedProcess M τ) P := hcM.stoppedProcess τ
  have hbs : ∀ᵐ ω ∂P, ∀ t, ‖stoppedProcess M τ t ω‖ ≤ C := by
    filter_upwards [hb] with ω hω t
    exact hω _
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  have hs := hSM.quadraticCovariation_stoppedProcess_left hA.isSemimartingale hF hτ
  apply hA.integrable_terminal_and_integral_eq_zero hMs hcs C hC hbs
  filter_upwards [hs, hlim] with ω hsω hlimω
  have he : (fun t : ℝ≥0 ↦
      (hMs.isSemimartingale_of_bound hF hcs C hbs).quadraticCovariation
        hA.isSemimartingale hF t ω) =
      fun t ↦ stoppedProcess (hSM.quadraticCovariation hA.isSemimartingale hF) τ t ω := by
    funext t
    change (hSM.stoppedProcess hF hτ).quadraticCovariation hA.isSemimartingale hF t ω = _
    exact hsω t
  rw [he]
  by_cases hτω : τ ω = ⊤
  · rw [stoppedValueWithTerminal_of_top hτω]
    simpa only [stoppedProcess, hτω, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hlimω
  · rw [stoppedValueWithTerminal_of_ne_top hτω]
    lift τ ω to ℝ≥0 using hτω with t ht
    apply tendsto_atTop_of_eventually_const (i₀ := t)
    intro s hts
    simp only [stoppedProcess, stoppedValue, ← ht, ← WithTop.coe_min,
      min_eq_right hts]

/-- A natural process has a uniformly integrable raw bracket with every
globally bounded càdlàg martingale. This is obtained from all stopped means,
not from a previously assumed martingale property of the bracket. -/
theorem IsNatural.isUIMartingale_quadraticCovariation
    {hF : F.IsUsual P} (hA : IsNatural A F P hF)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    IsUIMartingale
      ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
        hA.isSemimartingale hF) F P := by
  obtain ⟨Z, _, hlim, _⟩ := hA.exists_terminal_mean_zero M hM hcM C hC hb
  apply martingale_uniformIntegrable_of_zero_expected_stopping (Z := Z)
    ((hM.isSemimartingale_of_bound hF hcM C hb).adapted_quadraticCovariation
      hA.isSemimartingale hF)
  intro τ hτ
  exact hA.integrable_stoppedValueWithTerminal_quadraticCovariation_and_integral_eq_zero
    hM hcM C hC hb hlim hτ

/-- The true-martingale part of the natural bracket characterization. -/
theorem IsNatural.martingale_quadraticCovariation
    {hF : F.IsUsual P} (hA : IsNatural A F P hF)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    Martingale
      ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
        hA.isSemimartingale hF) F P :=
  (hA.isUIMartingale_quadraticCovariation hM hcM C hC hb).1

/-- Conversely, martingality of the actual bounded-test brackets implies
naturality. Their integrable terminals and L1 convergence are constructed
from integrable variation; no terminal or UI hypothesis is supplied. -/
theorem HasIntegrableVariation.isNatural_of_martingale_quadraticCovariation
    (hv : HasIntegrableVariation A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (h0 : A 0 =ᵐ[P] 0)
    (hQ : ∀ (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P)
      (hcM : HasCadlagPaths M P) (C : ℝ), 0 ≤ C →
      ∀ hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C,
      Martingale
        ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
          (hv.hasFiniteVariationPaths.isSemimartingale ha hF hc) hF) F P) :
    IsNatural A F P hF := by
  refine ⟨ha, hc, hv, h0, ?_⟩
  intro M hM hcM C hC hb
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let hSA := hv.hasFiniteVariationPaths.isSemimartingale ha hF hc
  have hi0 : Integrable (A 0) P := (integrable_zero Ω ℝ P).congr h0.symm
  obtain ⟨Z, hiZ, hlim, hL1, _⟩ :=
    hSM.exists_integrable_terminal_quadraticCovariation_of_right hSA hF hv hi0 hC hb
  have hm := hQ M hM hcM C hC hb
  refine ⟨Z, hiZ, hlim, ?_⟩
  have hQ0 : hSM.quadraticCovariation hSA hF 0 =ᵐ[P] 0 := by
    filter_upwards [hSM.quadraticCovariation_zero_ae hSA hF, h0] with ω hω h0ω
    simp only [hω, h0ω, Pi.zero_apply, mul_zero]
  have he (t : ℝ≥0) : (∫ ω, hSM.quadraticCovariation hSA hF t ω ∂P) = 0 := by
    calc
      _ = ∫ ω, P[hSM.quadraticCovariation hSA hF t | F 0] ω ∂P :=
        (integral_condExp (F.le 0)).symm
      _ = ∫ ω, hSM.quadraticCovariation hSA hF 0 ω ∂P :=
        integral_congr_ae (hm.condExp_ae_eq (show 0 ≤ t from bot_le))
      _ = 0 := by rw [integral_congr_ae hQ0]; simp only [Pi.zero_apply, integral_zero]
  have hmean := tendsto_integral_of_L1' Z hiZ.aestronglyMeasurable
    (Eventually.of_forall hm.integrable) hL1
  apply tendsto_nhds_unique hmean
  simpa only [he] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 ↦ (0 : ℝ)) atTop (𝓝 0))

/-- Naturality is equivalent to martingality of every actual bounded-test
raw bracket on the explicit adapted, cadlag, zero-initial IV domain. -/
theorem HasIntegrableVariation.isNatural_iff_martingale_quadraticCovariation
    (hv : HasIntegrableVariation A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (h0 : A 0 =ᵐ[P] 0) :
    IsNatural A F P hF ↔
      ∀ (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P)
        (hcM : HasCadlagPaths M P) (C : ℝ), 0 ≤ C →
        ∀ hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C,
        Martingale
          ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
            (hv.hasFiniteVariationPaths.isSemimartingale ha hF hc) hF) F P := by
  constructor
  · intro hA M hM hcM C hC hb
    exact hA.martingale_quadraticCovariation hM hcM C hC hb
  · exact hv.isNatural_of_martingale_quadraticCovariation ha hF hc h0

end ProbabilityTheory
