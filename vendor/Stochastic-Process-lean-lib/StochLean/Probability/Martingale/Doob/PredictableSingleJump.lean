/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.CenteredSingleJump
public import StochLean.Probability.Process.Stopping.PredictableAfterCoefficient
public import StochLean.Probability.Process.FiniteVariation.SingleJump
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Actual compensation of an integrable predictable single jump

The predictable compensating step has the explicit coefficient given by the
conditional expectation of the original coefficient before its lifetime. Its
actual total variation is integrable, with expectation bounded by the original
coefficient's first absolute moment. Subtracting it gives a true UI martingale.

The coefficient is only measurable at the stopping time, not before it. No
compensator, terminal variable, or convergence certificate is supplied as input.
An infinite lifetime never activates at finite time. Positivity is used only
to normalize the initial compensating value to zero almost surely.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}

/-- The actual before-conditional closed step is a predictable integrable-
variation compensator of an arbitrary L1 jump at a positive predictable lifetime. -/
theorem IsPredictableStoppingTime.exists_predictable_compensator_indicator
    (hτ : IsPredictableStoppingTime F τ P)
    (hc0 : IsCompleteSubMeasurableSpace P (F 0))
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] Z) (hi : Integrable Z P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      (∀ t : ℝ≥0, A t = {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
        P[Z | hτ.1.measurableSpaceBefore]) ∧
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧
      A 0 =ᵐ[P] 0 ∧ HasIntegrableVariation A P ∧
      (∫ ω, (eVariationOn (A · ω) univ).toReal ∂P) ≤ ∫ ω, ‖Z ω‖ ∂P ∧
      IsUIMartingale
        ((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) - A) F P := by
  classical
  let K := P[Z | hτ.1.measurableSpaceBefore]
  let A : ℝ≥0 → Ω → ℝ := fun t ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator K
  have hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K :=
    stronglyMeasurable_condExp
  have hiK : Integrable K P := integrable_condExp
  refine ⟨A, fun _ ↦ rfl,
    hK.isStronglyPredictable_indicator_stoppingTime_le hτ hc0,
    isCadlagPath_indicator_lifetime_le τ K, ?_,
    hasIntegrableVariation_indicator_lifetime_le hτ.1.measurable' hiK, ?_, ?_⟩
  · filter_upwards [hpos] with ω hω
    change {ω | τ ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator K ω = 0
    exact indicator_of_notMem
      (show ω ∉ {ω | τ ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)} from not_le.mpr hω) K
  · exact (integral_eVariationOn_indicator_lifetime_le hτ.1.measurable' hiK).trans
      (integral_norm_condExp_le Z)
  · have he : ((fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) - A) =
        (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (Z - K)) := by
      funext t
      change {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z -
        {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator K =
          {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (Z - K)
      exact (indicator_sub {ω | τ ω ≤ (t : WithTop ℝ≥0)} Z K).symm
    rw [he]
    exact isUIMartingale_indicator_sub_condExp_before hτ.1 hm hi

end ProbabilityTheory
