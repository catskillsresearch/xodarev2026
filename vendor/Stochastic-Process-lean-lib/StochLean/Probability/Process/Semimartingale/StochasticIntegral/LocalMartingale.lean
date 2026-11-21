/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocallyIntegrableVariationMartingale
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalL2
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance
public import StochLean.Probability.Process.LocalMartingale.Congr

/-! # Protter III.33: integration preserves local martingales

The actual fundamental decomposition splits the source into a locally
square-integrable local martingale and a local martingale of locally
integrable variation. The existing integral preserves local martingality on
each of these two proved domains. Its established integrator linearity and
indistinguishability invariance then identify their sum with the original
source integral.

Neither a decomposition nor a semimartingale certificate is an input to the
source theorem. The integrand needs only adaptedness and common-event caglad
paths: no global bound, initial moments, or source L2 assumption is added.
The second theorem uses any existing semimartingale witness for the same
integral; proof irrelevance introduces no new process or integral selector.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M H : ℝ≥0 → Ω → ℝ}

/-- The actual source stochastic integral of an adapted caglad process
against an arbitrary local martingale is a local martingale. -/
theorem IsLocalMartingale.isLocalMartingale_stochasticIntegral
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsLocalMartingale ((hM.isSemimartingale hF).stochasticIntegral hF ha hr) F P := by
  obtain ⟨N, D, hN, hD, _, _, hvD, he, _, hN2⟩ :=
    hM.exists_fundamental_decomposition_of_pos hF (β := 1) zero_lt_one
  let hSM := hM.isSemimartingale hF
  let hSN := hN.isSemimartingale hF
  let hSD := hD.isSemimartingale hF
  have hJN := hSN.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable
    hF hN2 ha hr
  have hJD := hD.isLocalMartingale_stochasticIntegral_of_locallyIntegrableVariation
    hF hvD ha hr
  have heND : Indistinguishable M (N + D) P :=
    Eventually.of_forall fun ω t ↦ congrFun (congrFun he t) ω
  have heJ := (hSM.stochasticIntegral_congr_integrator (hSN.add hSD) hF ha hr heND).trans
    (hSN.stochasticIntegral_add_integrator hSD hF ha hr)
  exact (hJN.add hJD hF).congr hF (hSM.adapted_stochasticIntegral hF ha hr) heJ.symm

/-- Any semimartingale proof for the same local-martingale integrator gives
the identical existing integral, so the source theorem applies unchanged. -/
theorem IsSemimartingale.isLocalMartingale_stochasticIntegral
    (hSM : IsSemimartingale M F P) (hF : F.IsUsual P)
    (hM : IsLocalMartingale M F P) (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsLocalMartingale (hSM.stochasticIntegral hF ha hr) F P :=
  hM.isLocalMartingale_stochasticIntegral hF ha hr

end ProbabilityTheory
