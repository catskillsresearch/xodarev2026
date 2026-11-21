/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegrableVariationMartingale
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialMask
public import StochLean.Probability.Process.Stopping.CagladLocalization
public import StochLean.Probability.Process.Stopping.InitialMask
public import StochLean.Probability.Process.LocalMartingale.Localization

/-! # Integrating a locally integrable-variation local martingale

The actual variation localizers are intersected with the existing initial-value
localizer, giving global IV and integrable initial values for the native masked
stopped sources. The integrand's bounded caglad cutoffs give actual true UI
integrals. Existing masked integral identities identify these with the joint
localization of the original integral. Native local-martingale localization
then removes all bounds and all initial moment assumptions.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A H : ℝ≥0 → Ω → ℝ}

/-- Caglad adapted integration preserves local martingality on the actual
locally integrable-variation domain, including arbitrary initial random values. -/
theorem IsLocalMartingale.isLocalMartingale_stochasticIntegral_of_locallyIntegrableVariation
    (hA : IsLocalMartingale A F P) (hF : F.IsUsual P)
    (hv : HasLocallyIntegrableVariation A F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsLocalMartingale ((hA.isSemimartingale hF).stochasticIntegral hF ha hr) F P := by
  classical
  let hSM := hA.isSemimartingale hF
  let J := hSM.stochasticIntegral hF ha hr
  obtain ⟨σ, hσ, hvσ⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hv
  let ι := initialValueLocalizer (A 0)
  have hι : IsLocalizingSequence F ι P :=
    (initialValueLocalizer_isFundamentalSequence (P := P) (hA.1 0)).isLocalizingSequence
  let ρ := min σ ι
  have hρ : IsLocalizingSequence F ρ P := hσ.min hι
  obtain ⟨τ, hτ, _, hbH⟩ := ha.exists_bounded_caglad_cutoffSequence hF hr
  have hcJ : HasCadlagPaths J P := hSM.hasCadlagPaths_stochasticIntegral hF ha hr
  have haJ : Adapted F J := hSM.adapted_stochasticIntegral hF ha hr
  apply isLocalMartingale_of_locally_cadlagUI hF hcJ
  refine ⟨min ρ τ, hρ.min hτ, fun n ↦ ?_⟩
  let Y := MeasureTheory.stoppedProcess
    (fun t ↦ {ω | 0 < ρ n ω}.indicator (A t)) (ρ n)
  have hYn : IsLocalMartingale Y F P := hA.masked_stoppedProcess hF (hρ.isStoppingTime n)
  have hvYn : HasIntegrableVariation Y P := by
    have haσ := hA.1.stronglyAdapted.stoppedProcess_of_usual hF
      hA.2.1.hasRightContinuousPaths (hσ.isStoppingTime n)
    have hs := (hvσ n).stoppedProcess haσ.adapted hF (hA.2.1.stoppedProcess (σ n))
      (hρ.isStoppingTime n)
    rw [stoppedProcess_stoppedProcess_of_le_right
      (show ρ n ≤ σ n from fun _ ↦ min_le_left _ _)] at hs
    exact (hasIntegrableVariation_stoppedProcess_indicator_pos_iff A (ρ n)).mpr hs
  have hbY0 : ∀ ω, ‖Y 0 ω‖ ≤ (n : ℝ) := by
    intro ω
    change ‖MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < ρ n ω}.indicator (A t)) (ρ n) 0 ω‖ ≤ (n : ℝ)
    rw [stoppedProcess_eq_of_le (i := (0 : ℝ≥0)) bot_le]
    by_cases hp : 0 < ρ n ω
    · rw [indicator_of_mem (show ω ∈ {ω | 0 < ρ n ω} from hp), Real.norm_eq_abs]
      by_contra hn
      have hle : ρ n ω ≤ ι n ω := min_le_right _ _
      simp only [ι, initialValueLocalizer, if_neg hn] at hle
      exact (not_le.mpr hp) hle
    · rw [indicator_of_notMem (show ω ∉ {ω | 0 < ρ n ω} from hp), norm_zero]
      exact Nat.cast_nonneg n
  have hiY0 : Integrable (Y 0) P :=
    memLp_one_iff_integrable.mp (MemLp.of_bound
      ((hYn.1 0).mono (F.le 0) le_rfl).aestronglyMeasurable (n : ℝ)
      (Eventually.of_forall hbY0))
  let K := fun t ↦ {ω | 0 < τ n ω}.indicator (cutoffIntegrand H (τ n) t)
  have haK : Adapted F K :=
    (adapted_cutoffIntegrand ha (hτ.isStoppingTime n)).indicator_initial
      ((hτ.isStoppingTime n).measurableSet_gt 0)
  have hrK : HasCagladPaths K P := (hr.cutoffIntegrand (τ n)).indicator _
  have hu := hYn.isUIMartingale_stochasticIntegral_of_integrableVariation hF hvYn hiY0
    haK hrK (Nat.cast_nonneg n) (hbH n)
  have he := (hSM.stochasticIntegral_masked_stoppedProcess hF haK hrK
    (hρ.isStoppingTime n)).trans
    (((hSM.stochasticIntegral_masked_cutoff hF ha hr (hτ.isStoppingTime n)).indicator
      {ω | 0 < ρ n ω}).stoppedProcess (ρ n))
  rw [masked_stoppedProcess_masked_stoppedProcess] at he
  have hκ : IsStoppingTime F (min (ρ n) (τ n)) :=
    (hρ.isStoppingTime n).min (hτ.isStoppingTime n)
  have ham := (haJ.indicator_initial (hκ.measurableSet_gt 0)).stronglyAdapted
  have hac := (ham.stoppedProcess_of_usual hF
    (hcJ.indicator _).hasRightContinuousPaths hκ).adapted
  exact ⟨hu.congr hac he, (hcJ.indicator _).stoppedProcess _⟩

end ProbabilityTheory
