/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.SingleJumpConditionalExpectation
public import StochLean.Probability.Process.Counting.SingleJumpRightContinuous
public import StochLean.Probability.Process.Filtration.ConditionalExpectationAugmentation

/-! # Single-jump information in the genuine usual augmentation

The raw closed-count natural filtration is already right-continuous.
Its usual augmentation is therefore precisely its restricted-lifetime
information plus ambient null sets, on the actually completed space.
The actual conditional expectation retains the original revealed-lifetime
and strict-survival formula. Endpoint atoms are not moved to survival.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0}

/-- Exact information after the genuine usual augmentation, including
the closed occurrence endpoint and all ambient null sets. -/
theorem usual_singleJumpCount_eq_sup_comap_restricted (hτ : Measurable τ) (t : ℝ≥0) :
    (Filtration.natural
      (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
      (stronglyMeasurable_singleJumpCount hτ)).usualAugmentation P t =
      MeasurableSpace.comap
        (restrictedStoppingTime τ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) inferInstance ⊔
          Filtration.nullSets P := by
  rw [Filtration.usualAugmentation_eq_withNullSets
    (natural_singleJumpCount_isRightContinuous hτ)]
  change _ ⊔ Filtration.nullSets P = _
  rw [natural_singleJumpCount_eq_comap_restricted hτ t]

/-- The actual usual-augmentation conditional expectation agrees with
the corrected raw single-jump formula. The probability and integrals on
the right remain those of the original lifetime law. -/
theorem condExp_usual_singleJumpCount [IsProbabilityMeasure P]
    (hτ : Measurable τ) {Y : Ω → ℝ} (hY : Integrable Y P)
    (t : ℝ≥0) (hSurvival : 0 < P.real {ω | (t : WithTop ℝ≥0) < τ ω}) :
    P.completion[(fun ω : NullMeasurableSpace Ω P ↦ Y ω) |
      (Filtration.natural
        (fun (s : ℝ≥0) ω ↦ if τ ω ≤ (s : WithTop ℝ≥0) then (1 : ℕ) else 0)
        (stronglyMeasurable_singleJumpCount hτ)).usualAugmentation P t] =ᵐ[P.completion]
      fun ω ↦ if τ ω ≤ (t : WithTop ℝ≥0) then
        P[Y | MeasurableSpace.comap τ inferInstance] ω
      else (∫ v in {v | (t : WithTop ℝ≥0) < τ v}, Y v ∂P) /
        P.real {v | (t : WithTop ℝ≥0) < τ v} := by
  exact (Filtration.condExp_usualAugmentation_of_isRightContinuous
    (natural_singleJumpCount_isRightContinuous hτ) hY t).trans
      (condExp_natural_singleJumpCount hτ hY t hSurvival)

end ProbabilityTheory
