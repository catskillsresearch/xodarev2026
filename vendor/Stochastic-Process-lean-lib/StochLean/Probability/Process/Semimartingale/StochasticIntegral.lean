/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Construction

/-! # The source Chapter II stochastic integral

This is the unique cadlag UCP limit of source elementary integrals, up to
indistinguishability. The selector is only available for a semimartingale
integrator and an adapted, common-event caglad integrand under usual conditions.
It is not a Chapter IV integral for arbitrary predictable processes.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) : ℝ≥0 → Ω → ℝ :=
  (hX.exists_stochasticIntegral hF ha hr).choose

theorem IsSemimartingale.adapted_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Adapted F (hX.stochasticIntegral hF ha hr) :=
  (hX.exists_stochasticIntegral hF ha hr).choose_spec.1

theorem IsSemimartingale.isCadlagPath_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (ω : Ω) :
    IsCadlagPath (hX.stochasticIntegral hF ha hr · ω) :=
  (hX.exists_stochasticIntegral hF ha hr).choose_spec.2.1 ω

theorem IsSemimartingale.hasCadlagPaths_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    HasCadlagPaths (hX.stochasticIntegral hF ha hr) P :=
  Eventually.of_forall (hX.isCadlagPath_stochasticIntegral hF ha hr)

theorem IsSemimartingale.tendstoUCP_stochasticIntegral_of_simple
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {S : ℕ → ℝ≥0 → Ω → ℝ} (hS : ∀ n, IsSimplePredictable (S n) F)
    (hu : TendstoUCP P S atTop H) :
    TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop
      (hX.stochasticIntegral hF ha hr) :=
  (hX.exists_stochasticIntegral hF ha hr).choose_spec.2.2 S hS hu

/-- Any cadlag limit of any legal simple approximation agrees with the selected integral. -/
theorem IsSemimartingale.stochasticIntegral_indistinguishable_of_limit
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {S : ℕ → ℝ≥0 → Ω → ℝ} (hS : ∀ n, IsSimplePredictable (S n) F)
    (hu : TendstoUCP P S atTop H) {J : ℝ≥0 → Ω → ℝ}
    (hJ : TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J)
    (hrJ : HasRightContinuousPaths J P) :
    Indistinguishable (hX.stochasticIntegral hF ha hr) J P :=
  (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS hu).indistinguishable_unique hJ
    (hX.hasCadlagPaths_stochasticIntegral hF ha hr).hasRightContinuousPaths hrJ

theorem IsSemimartingale.stochasticIntegral_indistinguishable_of_simple
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hH : IsSimplePredictable H F) :
    Indistinguishable (hX.stochasticIntegral hF ha hr) (hH.elementaryIntegralProcess X) P :=
  hX.stochasticIntegral_indistinguishable_of_limit hF ha hr (fun _ ↦ hH)
    (tendstoUCP_const atTop H) (tendstoUCP_const atTop (hH.elementaryIntegralProcess X))
    (hH.hasCadlagPaths_elementaryIntegralProcess hX.hasCadlagPaths).hasRightContinuousPaths

theorem IsSemimartingale.stochasticIntegral_proof_irrel
    (hX hX' : IsSemimartingale X F P) (hF hF' : F.IsUsual P)
    (ha ha' : Adapted F H) (hr hr' : HasCagladPaths H P) :
    hX.stochasticIntegral hF ha hr = hX'.stochasticIntegral hF' ha' hr' := rfl

end ProbabilityTheory
