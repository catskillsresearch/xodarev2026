/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorSignedTestsAE
public import StochLean.Probability.Process.FiniteVariation.CompensatorStochasticIntegral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance

/-! # The corrected III.19 consumer for the original AE-regular source

An everywhere-good increasing version is constructed only to interpret the
existing source Stieltjes kernel. The conclusion uses the original source's
actual Chapter II integral and the sole canonical compensator's actual
Chapter II integral, not replacement integral operators. Their equality of
expectations follows after the source's original initial product is removed.
The compensator starts at zero, so its actual integral needs no correction.

The expected absolute increment integral controls these quantities in L1.
It does not assert integrability of the source's initial product. Neither
the source nor the adapted caglad integrand must have good paths everywhere.
Kernel-fiber congruence makes the absolute condition independent of the
legitimate source version chosen here.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory.HasIntegrableVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Construct the actual III.19 signed-integral consumer on the common-AE
source domain. The only auxiliary path version interprets the source kernel;
both stochastic integrals in the conclusion use the original actual owners. -/
theorem exists_canonical_compensator_stochasticIntegral_tests_of_ae
    (hvX : HasIntegrableVariation X P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hmX : HasMonotonePaths X P)
    (hi0 : Integrable (X 0) P) :
    ∃ (Y : ℝ≥0 → Ω → ℝ) (haY : Adapted F Y)
      (hpathY : ∀ ω, IsCadlagPath (Y · ω) ∧ Monotone (Y · ω)),
      Indistinguishable X Y P ∧
      ∃ hSB : IsSemimartingale
        (hvX.hasLocallyIntegrableVariation.predictableCompensator haX hF hcX) F P,
        ∀ (H : ℝ≥0 → Ω → ℝ) (haH : Adapted F H) (hrH : HasCagladPaths H P) (T : ℝ≥0),
          (∫⁻ ω, ∫⁻ t in Ioc 0 T, ENNReal.ofReal ‖H t ω‖
            ∂totalVariationKernel Y haY
              (fun ω ↦ ((hpathY ω).2.monotoneOn univ).locallyBoundedVariationOn)
              (fun ω ↦ (hpathY ω).1.1) ω ∂P) < ∞ →
          let hSX := hvX.hasFiniteVariationPaths.isSemimartingale haX hF hcX
          Integrable (fun ω ↦ hSX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω) P ∧
            Integrable (hSB.stochasticIntegral hF haH hrH T) P ∧
            (∫ ω, hSX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω ∂P) =
              ∫ ω, hSB.stochasticIntegral hF haH hrH T ω ∂P := by
  obtain ⟨Y, haY, hpathY, heXY, A, hpA, hpathA, heBA, hA0, hvA, huXA, _⟩ :=
    hvX.exists_predictable_compensator_signed_tests_of_ae haX hF hcX hmX hi0
  let B := hvX.hasLocallyIntegrableVariation.predictableCompensator haX hF hcX
  obtain ⟨hpB, hcB, _, hvB, _⟩ :=
    hvX.hasLocallyIntegrableVariation.predictableCompensator_properties haX hF hcX
  have hSB : IsSemimartingale B F P := hvB.hasFiniteVariationPaths.isSemimartingale
    hpB.stronglyAdapted.adapted hF (Eventually.of_forall hcB)
  refine ⟨Y, haY, hpathY, heXY, hSB, ?_⟩
  intro H haH hrH T habs hSX
  have hcY : HasCadlagPaths Y P := Eventually.of_forall fun ω ↦ (hpathY ω).1
  have hcA : HasCadlagPaths A P := Eventually.of_forall fun ω ↦ (hpathA ω).1
  have haA := hpA.stronglyAdapted.adapted
  have hvY : HasIntegrableVariation Y P := hvX.congr heXY
  have hiY0 : Integrable (Y 0) P := hi0.congr (heXY.ae_eq 0)
  have hiA0 : Integrable (A 0) P := by rw [hA0]; exact integrable_zero _ _ _
  have huYA : IsUIMartingale (Y - A) F P := by
    apply huXA.congr (haY.sub haA)
    filter_upwards [heXY] with ω hω t
    change X t ω - A t ω = Y t ω - A t ω
    rw [hω t]
  have ht := integrable_and_integral_stochasticIntegral_sub_initial_eq_of_martingale_sub
    haY (fun ω ↦ (hpathY ω).1) (fun ω ↦ (hpathY ω).2)
    haA (fun ω ↦ (hpathA ω).1) (fun ω ↦ (hpathA ω).2)
    (hvY.integrable haY hF hcY hiY0) (hvA.integrable haA hF hcA hiA0)
    hvY huYA.1 hF haH hrH T habs
  let hSY := hvY.hasFiniteVariationPaths.isSemimartingale haY hF hcY
  let hSA := hvA.hasFiniteVariationPaths.isSemimartingale haA hF hcA
  have heX : (fun ω ↦ hSX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω) =ᵐ[P]
      fun ω ↦ hSY.stochasticIntegral hF haH hrH T ω - H 0 ω * Y 0 ω := by
    filter_upwards [hSX.stochasticIntegral_congr_integrator hSY hF haH hrH heXY,
      heXY] with ω hω hYω
    rw [hω T, hYω 0]
  have heB : hSB.stochasticIntegral hF haH hrH T =ᵐ[P]
      fun ω ↦ hSA.stochasticIntegral hF haH hrH T ω - H 0 ω * A 0 ω := by
    filter_upwards [hSB.stochasticIntegral_congr_integrator hSA hF haH hrH heBA] with ω hω
    simp only [hω T, hA0, Pi.zero_apply, mul_zero, sub_zero]
  exact ⟨ht.1.congr heX.symm, ht.2.1.congr heB.symm,
    (integral_congr_ae heX).trans (ht.2.2.trans (integral_congr_ae heB.symm))⟩

end ProbabilityTheory.HasIntegrableVariation
