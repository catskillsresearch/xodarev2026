/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.PredictableIntegrator
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationPreservation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue
public import StochLean.Probability.Process.FiniteVariation.PredictableLocallyIntegrable
public import StochLean.Probability.Process.FiniteVariation.CompensatorPredictable

/-! # Actual compensation of integrals against predictable FV processes

The sole Chapter II integral has a genuinely predictable version. Finite
variation transfers to this version, whose actual predictable localization
gives locally integrable variation. Both properties transfer back to the
original selected integral. Canonical compensation and full version
uniqueness then identify its compensator with the integral minus the
original initial product. No initial moment or coefficient bound is assumed.

This is a prerequisite for the corrected III.20 application, not yet its
right-versus-left Stieltjes identity. The integrand remains in the original
adapted common-AE caglad domain, not the general predictable domain.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

/-- The actual integral against a predictable FV source is locally IV,
without a supplied integral-variation certificate or an initial moment. -/
theorem hasLocallyIntegrableVariation_stochasticIntegral_of_predictable
    (hX : IsSemimartingale X F P) (hpX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (hvX : HasFiniteVariationPaths X P) (ha : Adapted F H) (hc : HasCagladPaths H P) :
    HasLocallyIntegrableVariation (hX.stochasticIntegral hF ha hc) F P := by
  obtain ⟨J, he, hpJ, hcJ⟩ :=
    hX.exists_predictable_stochasticIntegral_of_predictable hpX hF ha hc
  have hvJ := (hX.hasFiniteVariationPaths_stochasticIntegral hF hvX ha hc).congr he
  exact (hpJ.hasLocallyIntegrableVariation hF hcJ hvJ).congr he.symm

/-- Compensation of the actual selected integral subtracts exactly its
original initial product, even when that product is not integrable. -/
theorem predictableCompensator_stochasticIntegral_of_predictable
    (hX : IsSemimartingale X F P) (hpX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (hvX : HasFiniteVariationPaths X P) (ha : Adapted F H) (hc : HasCagladPaths H P) :
    let hvI := hX.hasLocallyIntegrableVariation_stochasticIntegral_of_predictable
      hpX hF hvX ha hc
    Indistinguishable
      (hvI.predictableCompensator (hX.adapted_stochasticIntegral hF ha hc) hF
        (hX.hasCadlagPaths_stochasticIntegral hF ha hc))
      (fun t ω ↦ hX.stochasticIntegral hF ha hc t ω - H 0 ω * X 0 ω) P := by
  intro hvI
  obtain ⟨J, he, hpJ, hcJ⟩ :=
    hX.exists_predictable_stochasticIntegral_of_predictable hpX hF ha hc
  have haJ := hpJ.stronglyAdapted.adapted
  have hvJ : HasLocallyIntegrableVariation J F P := hvI.congr he
  have hcomp := hvI.predictableCompensator_congr hvJ
    (hX.adapted_stochasticIntegral hF ha hc) haJ hF
    (hX.hasCadlagPaths_stochasticIntegral hF ha hc) hcJ he
  have hself := hvJ.predictableCompensator_eq_sub_initial_of_predictable haJ hF hcJ hpJ
  apply (hcomp.trans hself).trans
  filter_upwards [he, hX.stochasticIntegral_zero_ae hF ha hc] with ω hω h0 t
  change J t ω - J 0 ω = hX.stochasticIntegral hF ha hc t ω - H 0 ω * X 0 ω
  rw [← hω t, ← hω 0, h0]

end ProbabilityTheory.IsSemimartingale
