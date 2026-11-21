/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorInitial

/-! # Compensator construction with an arbitrary initial random value

A measurable finite initial random value, even when not integrable, gives a
constant process with zero variation. We invoke the actual general local
compensator construction and then identify its output with zero by uniqueness.
The remainder is a Protter local martingale, but cannot be a true UI
martingale when the original initial value is not integrable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ}

/-- Actual local compensator construction preserves arbitrary initial data.
Its initial masks are essential when that data is not integrable. -/
theorem exists_predictable_compensator_arbitrary_initial_constant
    (hF : F.IsUsual P) (hmZ : Measurable[F 0] Z) :
    let X : ℝ≥0 → Ω → ℝ := fun _ ↦ Z
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasLocallyIntegrableVariation A F P ∧ IsLocalMartingale (X - A) F P ∧
      Indistinguishable A 0 P ∧
      (¬ Integrable Z P → ¬ IsUIMartingale (X - A) F P) := by
  let X : ℝ≥0 → Ω → ℝ := fun _ ↦ Z
  have ha : Adapted F X := fun _ ↦ hmZ.mono (F.mono bot_le) le_rfl
  have hc : HasCadlagPaths X P := Eventually.of_forall fun _ ↦
    IsContinuousPath.isCadlagPath continuous_const
  have hv : HasLocallyIntegrableVariation X F P :=
    (hasIntegrableVariation_const Z).hasLocallyIntegrableVariation
  obtain ⟨A, hpA, hcA, hA0, hvA, hM, huniq⟩ :=
    hv.exists_unique_predictable_compensator ha hF hc
  have hXlocal : IsLocalMartingale X F P :=
    (isContinuousLocalMartingale_const_initial hmZ).1
  have ha0 : Adapted F (0 : ℝ≥0 → Ω → ℝ) := fun _ ↦ measurable_const
  have hp0 : IsStronglyPredictable F (0 : ℝ≥0 → Ω → ℝ) :=
    ha0.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  have h0local : IsLocalMartingale (X - 0) F P := by
    simpa only [sub_zero] using hXlocal
  have he : Indistinguishable A 0 P :=
    huniq 0 hp0 (hasIntegrableVariation_const (0 : Ω → ℝ)).hasFiniteVariationPaths
      (Eventually.of_forall fun _ ↦ rfl) h0local
  refine ⟨A, hpA, hcA, hA0, hvA, hM, he, ?_⟩
  intro hni hui
  have hi := hui.1.integrable 0
  change Integrable (Z - A 0) P at hi
  rw [hA0, sub_zero] at hi
  exact hni hi

end ProbabilityTheory
