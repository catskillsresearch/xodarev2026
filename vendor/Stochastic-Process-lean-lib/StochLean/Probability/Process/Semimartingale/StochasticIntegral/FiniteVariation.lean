/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Algebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance
public import StochLean.Probability.Process.FiniteVariation.UCP

/-! # Agreement of the general integral with the pathwise finite-variation owner

Source simple agreement and proved FV UCP continuity identify the constructed
general integral. Caglad integrands need only have regular paths on one common
full-measure event; a usual initial null-set reset reduces to the everywhere case.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_eq_finiteVariationIntegral_of_everywhere_caglad
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hv : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hrX : ∀ ω, IsRightContinuousPath (X · ω)) (ha : Adapted F H)
    (hr : ∀ ω, IsCagladPath (H · ω)) :
    Indistinguishable (hX.stochasticIntegral hF ha (Eventually.of_forall hr))
      (finiteVariationIntegral X hv hrX H) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF (Eventually.of_forall hr)
  apply hX.stochasticIntegral_indistinguishable_of_limit hF _ _ hS huS
  · exact tendstoUCP_elementaryIntegral_of_finiteVariation X hv hrX hX.adapted hS ha hr huS
  · exact Eventually.of_forall fun ω ↦
      (isCadlagPath_pathStieltjesIntegral
        (fun T ↦ integrableOn_variationStieltjes_of_adapted_caglad X hv hrX ha hr T ω)).1

theorem IsSemimartingale.stochasticIntegral_eq_finiteVariationIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hv : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hrX : ∀ ω, IsRightContinuousPath (X · ω))
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable (hX.stochasticIntegral hF ha hr)
      (finiteVariationIntegral X hv hrX H) P := by
  classical
  let good : Set Ω := {ω | IsCagladPath (H · ω)}
  have hbad : MeasurableSet[F 0] goodᶜ := hF.complete_initial goodᶜ (ae_iff.mp hr)
  have hgood : MeasurableSet[F 0] good := by simpa only [compl_compl] using hbad.compl
  let K : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ good then H t ω else 0
  have hKa : Adapted F K := fun t ↦
    Measurable.ite (F.mono bot_le _ hgood) (ha t) measurable_const
  have hKr : ∀ ω, IsCagladPath (K · ω) := by
    intro ω
    by_cases hω : ω ∈ good
    · simpa only [K, if_pos hω] using (show IsCagladPath (H · ω) from hω)
    · simpa only [K, if_neg hω] using
        (IsContinuousPath.isCagladPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
  have hHK : Indistinguishable H K P := by
    filter_upwards [hr] with ω hω t
    exact (if_pos (show ω ∈ good from hω)).symm
  have hJK := hX.stochasticIntegral_congr_integrand hF ha hr hKa
    (Eventually.of_forall hKr) hHK
  have hKV := hX.stochasticIntegral_eq_finiteVariationIntegral_of_everywhere_caglad
    hF hv hrX hKa hKr
  apply (hJK.trans hKV).trans
  filter_upwards [hHK.symm] with ω hω t
  change pathStieltjesIntegral (X · ω) (hv ω) (hrX ω) (K · ω) t =
    pathStieltjesIntegral (X · ω) (hv ω) (hrX ω) (H · ω) t
  rw [show (K · ω) = (H · ω) from funext hω]

/-- Protter II.17 on common-event finite-variation paths of the original integrator.
The source integral is compared with its actual pathwise Stieltjes integral; no
everywhere finite-variation version is required as input. -/
theorem IsSemimartingale.stochasticIntegral_eq_pathStieltjesIntegral_ae
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, ∃ hωv : LocallyBoundedVariationOn (X · ω) univ,
      ∃ hωr : IsCadlagPath (X · ω), ∀ t,
        hX.stochasticIntegral hF ha hr t ω =
          pathStieltjesIntegral (X · ω) hωv hωr.1 (H · ω) t := by
  classical
  let good : Set Ω := {ω | LocallyBoundedVariationOn (X · ω) univ ∧ IsCadlagPath (X · ω)}
  have hg : ∀ᵐ ω ∂P, ω ∈ good := hv.and hX.hasCadlagPaths
  have hbad : MeasurableSet[F 0] goodᶜ := hF.complete_initial goodᶜ (ae_iff.mp hg)
  have hgood : MeasurableSet[F 0] good := by simpa only [compl_compl] using hbad.compl
  let Z : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ good then X t ω else 0
  have hZa : Adapted F Z := fun t ↦
    Measurable.ite (F.mono bot_le _ hgood) (hX.adapted t) measurable_const
  have hZv : ∀ ω, LocallyBoundedVariationOn (Z · ω) univ := by
    intro ω
    by_cases hω : ω ∈ good
    · simpa only [Z, if_pos hω] using hω.1
    · have hm := (monotone_const : Monotone (fun _ : ℝ≥0 ↦ (0 : ℝ))).monotoneOn univ
      simpa only [Z, if_neg hω] using hm.locallyBoundedVariationOn
  have hZr : ∀ ω, IsCadlagPath (Z · ω) := by
    intro ω
    by_cases hω : ω ∈ good
    · simpa only [Z, if_pos hω] using hω.2
    · simpa only [Z, if_neg hω] using
        (IsContinuousPath.isCadlagPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
  have hXZ : Indistinguishable X Z P := by
    filter_upwards [hg] with ω hω t
    exact (if_pos hω).symm
  have hZ : IsSemimartingale Z F P :=
    (show HasFiniteVariationPaths Z P from Eventually.of_forall hZv).isSemimartingale
      hZa hF (Eventually.of_forall hZr)
  have hJV := (hX.stochasticIntegral_congr_integrator hZ hF ha hr hXZ).trans
    (hZ.stochasticIntegral_eq_finiteVariationIntegral hF hZv (fun ω ↦ (hZr ω).1) ha hr)
  filter_upwards [hg, hJV] with ω hω hJVω
  refine ⟨hω.1, hω.2, fun t ↦ ?_⟩
  rw [hJVω t]
  simp only [finiteVariationIntegral, Z, if_pos hω]

end ProbabilityTheory
