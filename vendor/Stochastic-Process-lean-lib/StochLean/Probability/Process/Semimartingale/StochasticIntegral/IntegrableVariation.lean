/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue
public import StochLean.Probability.Process.FiniteVariation.IntegrableTerminal
public import StochLean.Probability.Process.Path.CagladMeasurable
public import StochLean.Analysis.PathVariation.StieltjesIntegralVariation

/-! # Integrable variation of the actual stochastic integral

For an integrable-variation integrator and a caglad adapted integrand bounded
at positive times, the actual Chapter II stochastic integral has integrable
variation. The proof uses its already established pathwise Stieltjes identity.
The initial product is retained and needs independent L1 control for terminal
limits and Class D; no boundedness of the integrand at zero is required.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A H : ℝ≥0 → Ω → ℝ}

/-- Positive-time bounds control actual extended variation, including when
the integrator has infinite variation on the entire half-line. -/
theorem IsSemimartingale.ae_eVariationOn_stochasticIntegral_le_of_finiteVariation
    (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths A P) (ha : Adapted F H) (hr : HasCagladPaths H P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, 0 < t → ‖H t ω‖ ≤ C) :
    ∀ᵐ ω ∂P, eVariationOn (hA.stochasticIntegral hF ha hr · ω) univ ≤
      ENNReal.ofReal C * eVariationOn (A · ω) univ := by
  filter_upwards [hA.stochasticIntegral_eq_pathStieltjesIntegral_ae hF hv ha hr, hr, hb]
    with ω hI hH hbound
  obtain ⟨hvω, hcω, he⟩ := hI
  rw [show (hA.stochasticIntegral hF ha hr · ω) =
    pathStieltjesIntegral (A · ω) hvω hcω.1 (H · ω) from funext he]
  exact eVariationOn_pathStieltjesIntegral_univ_le hH.measurable hC hbound

/-- Actual integrable variation, not merely integrability of the totalized
real value of an extended variation, is preserved. -/
theorem IsSemimartingale.hasIntegrableVariation_stochasticIntegral
    (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasIntegrableVariation A P) (ha : Adapted F H) (hr : HasCagladPaths H P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, 0 < t → ‖H t ω‖ ≤ C) :
    HasIntegrableVariation (hA.stochasticIntegral hF ha hr) P := by
  have hbound := hA.ae_eVariationOn_stochasticIntegral_le_of_finiteVariation
    hF hv.hasFiniteVariationPaths ha hr hC hb
  have hfinite : ∀ᵐ ω ∂P, ENNReal.ofReal C * eVariationOn (A · ω) univ ≠ ∞ :=
    hv.ae_eVariationOn_ne_top.mono fun _ hω ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω
  constructor
  · filter_upwards [hbound, hfinite] with ω hω hf
    exact ne_top_of_le_ne_top hf hω
  · apply (hv.integrable_eVariationOn_toReal.const_mul C).mono'
      (((hA.adapted_stochasticIntegral hF ha hr).measurable_eVariationOn_univ_of_usual
        hF (hA.hasCadlagPaths_stochasticIntegral hF ha hr)).ennreal_toReal).aestronglyMeasurable
    filter_upwards [hbound, hfinite] with ω hω hf
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have ht := ENNReal.toReal_mono hf hω
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using ht

/-- Independent integrability of the actual initial product closes the
terminal and Class D conclusions, even if the initial integrand is unbounded. -/
theorem IsSemimartingale.exists_integrable_terminal_stochasticIntegral_of_integrableVariation
    (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasIntegrableVariation A P) (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hi0 : Integrable (fun ω ↦ H 0 ω * A 0 ω) P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, 0 < t → ‖H t ω‖ ≤ C) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (hA.stochasticIntegral hF ha hr · ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (hA.stochasticIntegral hF ha hr t - Z) 1 P)
        atTop (𝓝 0) ∧ IsClassD (hA.stochasticIntegral hF ha hr) F P := by
  have hiI0 := hi0.congr (hA.stochasticIntegral_zero_ae hF ha hr).symm
  have hvI := hA.hasIntegrableVariation_stochasticIntegral hF hv ha hr hC hb
  obtain ⟨Z, hiZ, hl, hL, hD, _, _⟩ := hvI.exists_integrable_terminal
    (hA.adapted_stochasticIntegral hF ha hr) hF
    (hA.hasCadlagPaths_stochasticIntegral hF ha hr) hiI0
  exact ⟨Z, hiZ, hl, hL, hD⟩

end ProbabilityTheory
