/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.RegularStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Conditional centering from all predictable jump-mean tests

Testing every positive predictable lifetime also tests its restrictions to
events known strictly before it. The explicit zero-terminal restriction
identity therefore upgrades zero jump means to zero conditional jump means.
Actual jump integrability is required separately before identifying a
conditional expectation; a default Bochner value is not used as a substitute.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- Restriction tests identify the actual integrable jump's conditional mean
before a predictable lifetime. No path or martingale hypothesis is needed. -/
theorem condExp_stopped_jump_before_ae_eq_zero_of_predictable_jump_mean_zero
    (hF : F.IsUsual P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hi : Integrable (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) P) :
    P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ |
      hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hτ.1.measurableSpaceBefore_le_ambient hi
    (fun _ _ _ ↦ (integrable_zero Ω ℝ P).integrableOn) _ aestronglyMeasurable_zero
  intro A hA _
  have hp : ∀ᵐ ω ∂P, 0 < restrictedStoppingTime τ A ω :=
    hpos.mono fun ω hω ↦ hω.trans_le (le_restrictedStoppingTime τ A ω)
  have he := hreg _ (hτ.restrictedStoppingTime_before hF hA) hp
  rw [stoppedValueWithTerminal_zero_restrictedStoppingTime,
    integral_indicator (hτ.1.measurableSpaceBefore_le_ambient A hA)] at he
  simpa only [Pi.zero_apply, integral_zero] using he.symm

end MeasureTheory
