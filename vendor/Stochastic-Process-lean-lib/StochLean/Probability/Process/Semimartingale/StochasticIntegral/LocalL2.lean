/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.BoundedL2
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialMask
public import StochLean.Probability.Process.Stopping.CagladLocalization
public import StochLean.Probability.Process.Stopping.InitialMask
public import StochLean.Probability.Process.LocalMartingale.SquareStability
public import StochLean.Probability.Process.LocalMartingale.Localization

/-! # Protter II.20: locally square-integrable martingale preservation

The integrator's L2 localizers and the integrand's norm-exit localizers are combined
by their pointwise minimum. Bounded integration of the first masked process against
the second masked cutoff is exactly this joint localization of the final integral.
No integrability or vanishing assumption on the unmasked initial value is required.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.locally_squareIntegrableMartingale_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F
      (hX.stochasticIntegral hF ha hr) P := by
  obtain ⟨σ, hσ, hM⟩ := hL
  obtain ⟨τ, hτ, _, hb⟩ := ha.exists_bounded_caglad_cutoffSequence hF hr
  refine ⟨min σ τ, hσ.min hτ, fun n ↦ ?_⟩
  have hσn := hσ.isStoppingTime n
  have hτn := hτ.isStoppingTime n
  let K := fun t ↦ {ω | 0 < τ n ω}.indicator (cutoffIntegrand H (τ n) t)
  have haK : Adapted F K :=
    (adapted_cutoffIntegrand ha hτn).indicator_initial (hτn.measurableSet_gt 0)
  have hrK : HasCagladPaths K P := (hr.cutoffIntegrand (τ n)).indicator _
  have hSM := (hX.indicator_initial (hσn.measurableSet_gt 0)).stoppedProcess hF hσn
  have hI := hSM.isSquareIntegrableMartingale_stochasticIntegral_of_bounded
    hF (hM n) haK hrK n (by exact_mod_cast hb n)
  have heq := (hX.stochasticIntegral_masked_stoppedProcess hF haK hrK hσn).trans
    (((hX.stochasticIntegral_masked_cutoff hF ha hr hτn).indicator
      {ω | 0 < σ n ω}).stoppedProcess (σ n))
  rw [masked_stoppedProcess_masked_stoppedProcess] at heq
  apply hI.congr ?_ heq
  have hρ : IsStoppingTime F (min (σ n) (τ n)) := hσn.min hτn
  exact (((hX.adapted_stochasticIntegral hF ha hr).indicator_initial
    (hρ.measurableSet_gt 0)).stronglyAdapted.stoppedProcess_of_usual hF
      ((hX.hasCadlagPaths_stochasticIntegral hF ha hr).indicator _).hasRightContinuousPaths
      hρ).adapted

theorem IsSemimartingale.locally_squareIntegrableMartingale_stochasticIntegral_of_squareIntegrable
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hM : IsSquareIntegrableMartingale X F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F
      (hX.stochasticIntegral hF ha hr) P :=
  hX.locally_squareIntegrableMartingale_stochasticIntegral hF (Locally.of_prop hM) ha hr

theorem IsSemimartingale.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsLocalMartingale (hX.stochasticIntegral hF ha hr) F P :=
  isLocalMartingale_of_locally_squareIntegrableMartingale hF
    (hX.hasCadlagPaths_stochasticIntegral hF ha hr)
    (hX.locally_squareIntegrableMartingale_stochasticIntegral hF hL ha hr)

end ProbabilityTheory
