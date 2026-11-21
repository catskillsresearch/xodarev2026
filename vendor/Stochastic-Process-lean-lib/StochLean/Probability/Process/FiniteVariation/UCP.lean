/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Continuity
public import StochLean.Probability.Process.FiniteVariation.SimpleAgreement
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Regularity
public import StochLean.Probability.Process.UCP.UniformConvergence

/-! # UCP continuity of finite-variation integration on the source caglad class

Pathwise bounds may depend on the sample and need not be integrable. The proof
uses actual locally uniform subsequences and measurable output deviations.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

theorem tendstoUCP_finiteVariationIntegral_of_caglad (ha : Adapted F X)
    {H : ℕ → ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℝ}
    (hHa : ∀ n, Adapted F (H n)) (hHc : ∀ n ω, IsCagladPath (fun t ↦ H n t ω))
    (hGa : Adapted F G) (hGc : ∀ ω, IsCagladPath (fun t ↦ G t ω))
    (hHG : TendstoUCP P H atTop G) :
    TendstoUCP P (fun n ↦ finiteVariationIntegral X hv hr (H n)) atTop
      (finiteVariationIntegral X hv hr G) := by
  have hmH (n : ℕ) :=
    isStronglyProgressive_finiteVariationIntegral_of_caglad X hv hr ha (hHa n) (hHc n)
  have hmG := isStronglyProgressive_finiteVariationIntegral_of_caglad X hv hr ha hGa hGc
  have hrH (n : ℕ) (ω : Ω) :
      IsRightContinuousPath (fun t ↦ finiteVariationIntegral X hv hr (H n) t ω) :=
    (isCadlagPath_pathStieltjesIntegral
      (fun T ↦ integrableOn_variationStieltjes_of_adapted_caglad X hv hr (hHa n) (hHc n) T ω)).1
  have hrG (ω : Ω) : IsRightContinuousPath (fun t ↦ finiteVariationIntegral X hv hr G t ω) :=
    (isCadlagPath_pathStieltjesIntegral
      (fun T ↦ integrableOn_variationStieltjes_of_adapted_caglad X hv hr hGa hGc T ω)).1
  apply tendstoUCP_of_subseq_ae_compactDeviation
    (fun n T ↦ measurable_compactDeviation
      (fun _ ↦ (hmH n).stronglyAdapted.adapted.measurable)
      (fun _ ↦ hmG.stronglyAdapted.adapted.measurable) (hrH n) hrG T)
  intro ns hns
  obtain ⟨k, _, hk⟩ := (hHG.comp hns).exists_seq_ae_locallyUniform
  refine ⟨k, hk.mono fun ω hω T ↦ ?_⟩
  apply tendsto_compactDeviation_iff_tendstoUniformlyOn.mpr
  exact tendstoUniformlyOn_finiteVariationIntegral_of_caglad X hv hr
    (fun n ↦ hHa (ns (k n))) (fun n ↦ hHc (ns (k n))) hGa hGc
    (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hω T))

/-- Whenever source simple approximations are given, their elementary integrals converge
to the constructed pathwise FV integral. This does not assert the still-separate density theorem. -/
theorem tendstoUCP_elementaryIntegral_of_finiteVariation (ha : Adapted F X)
    {H : ℕ → ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℝ}
    (hH : ∀ n, IsSimplePredictable (H n) F)
    (hGa : Adapted F G) (hGc : ∀ ω, IsCagladPath (fun t ↦ G t ω))
    (hHG : TendstoUCP P H atTop G) :
    TendstoUCP P (fun n T ω ↦ (hH n).elementaryIntegral (fun t ω ↦ X (min t T) ω) ω)
      atTop (finiteVariationIntegral X hv hr G) := by
  have heq : (fun n T ω ↦ (hH n).elementaryIntegral (fun t ω ↦ X (min t T) ω) ω) =
      fun n ↦ finiteVariationIntegral X hv hr (H n) := by
    funext n T ω
    exact ((hH n).finiteVariationIntegral_eq X hv hr T ω).symm
  rw [heq]
  exact tendstoUCP_finiteVariationIntegral_of_caglad X hv hr ha
    (fun n ↦ (hH n).adapted) (fun n ↦ (hH n).isCagladPath) hGa hGc hHG

end ProbabilityTheory
