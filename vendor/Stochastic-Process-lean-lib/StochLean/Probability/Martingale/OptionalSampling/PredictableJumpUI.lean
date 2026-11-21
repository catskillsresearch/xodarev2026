/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.AnnouncingBefore
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUnbounded
public import StochLean.Probability.Process.Stopping.AnnouncingStability

/-! # UI martingale jumps at almost surely finite predictable times

Uniform integrability permits actual optional sampling at an unbounded,
almost surely finite predictable stopping time. Sampling at its actual
announcing times supplies the conditional identities required by the common
announcing-limit theorem; these identities are not final hypotheses.

The stopped value, left limit, and jump are all actually integrable. The jump
has zero conditional mean given the native before-field, not necessarily
zero value. Positive time is retained because of the source initial-jump
convention. All pathwise finite evaluations are justified on the common
almost-sure finite event; nothing is asserted at an infinite lifetime.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- The native UI stopping family gives actual stopped-value integrability
under usualness, without imposing everywhere finiteness or progressiveness. -/
theorem integrable_stoppedValue_of_ae_finite_usual
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths M P) (hτ : IsStoppingTime F τ)
    (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) : Integrable (stoppedValue M τ) P :=
  memLp_one_iff_integrable.mp
    ((hM.uniformIntegrable_stoppedValue_of_ae_finite_usual hu hF hr
      (ι := Unit) (τ := fun _ ↦ τ) (fun _ ↦ hτ) (fun _ ↦ hfinite)).memLp ())

/-- Actual UI optional sampling supplies the announcing CE identities,
which identify the stopped left limit at an AE-finite predictable time. -/
theorem stopped_leftLimit_ae_eq_condExp_before_of_predictable_of_ae_finite
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    stoppedValue (leftLimitProcess M) τ =ᵐ[P]
      P[stoppedValue M τ | hτ.1.measurableSpaceBefore] := by
  obtain ⟨σ, hs, hle⟩ := hτ.exists_announcing_le
  apply hs.stopped_leftLimit_ae_eq_condExp_before hτ.1 hF.complete_initial hc hpos hfinite
  intro n
  exact hM.stoppedValue_ae_eq_condExp_of_ae_finite_usual hu hF hc.hasRightContinuousPaths
    (hs.isStoppingTime n) hτ.1 (Eventually.of_forall (hle n)) hfinite

/-- Integrability of the actual left limit follows from the CE identity. -/
theorem integrable_stopped_leftLimit_of_predictable_of_ae_finite
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Integrable (stoppedValue (leftLimitProcess M) τ) P :=
  integrable_condExp.congr
    (hM.stopped_leftLimit_ae_eq_condExp_before_of_predictable_of_ae_finite
      hu hF hc hτ hpos hfinite).symm

/-- Both terms of the actual jump have now been proved integrable. -/
theorem integrable_stopped_jump_of_predictable_of_ae_finite
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Integrable (stoppedValue (jumpProcess M) τ) P := by
  change Integrable (stoppedValue M τ - stoppedValue (leftLimitProcess M) τ) P
  exact (hM.integrable_stoppedValue_of_ae_finite_usual
      hu hF hc.hasRightContinuousPaths hτ.1 hfinite).sub
    (hM.integrable_stopped_leftLimit_of_predictable_of_ae_finite hu hF hc hτ hpos hfinite)

/-- An AE-finite positive predictable stopping time has zero conditional jump
mean for a UI martingale. No actual zero-jump claim follows from this result. -/
theorem condExp_stopped_jump_before_ae_eq_zero_of_predictable_of_ae_finite
    (hM : Martingale M F P) (hu : UniformIntegrable M 1 P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths M P) (hτ : IsPredictableStoppingTime F τ P)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    P[stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
  have hi := hM.integrable_stoppedValue_of_ae_finite_usual
    hu hF hc.hasRightContinuousPaths hτ.1 hfinite
  have hl := hM.integrable_stopped_leftLimit_of_predictable_of_ae_finite hu hF hc hτ hpos hfinite
  have he := hM.stopped_leftLimit_ae_eq_condExp_before_of_predictable_of_ae_finite
    hu hF hc hτ hpos hfinite
  have hce : P[stoppedValue (leftLimitProcess M) τ | hτ.1.measurableSpaceBefore] =ᵐ[P]
      P[stoppedValue M τ | hτ.1.measurableSpaceBefore] :=
    (condExp_congr_ae he).trans
      (condExp_condExp_of_le le_rfl hτ.1.measurableSpaceBefore_le_ambient)
  change P[stoppedValue M τ - stoppedValue (leftLimitProcess M) τ |
    hτ.1.measurableSpaceBefore] =ᵐ[P] 0
  filter_upwards [condExp_sub hi hl hτ.1.measurableSpaceBefore, hce] with ω hlin hω
  change _ = (0 : ℝ)
  rw [hlin]
  change P[stoppedValue M τ | hτ.1.measurableSpaceBefore] ω -
    P[stoppedValue (leftLimitProcess M) τ | hτ.1.measurableSpaceBefore] ω = 0
  rw [hω, sub_self]

end MeasureTheory.Martingale
