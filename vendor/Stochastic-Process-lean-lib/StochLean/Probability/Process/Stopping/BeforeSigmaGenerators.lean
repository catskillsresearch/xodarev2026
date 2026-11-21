/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PredictableValue
public import StochLean.Probability.Process.Measurability.PredictableGenerators

/-! # Predictable-value generators of the pre-stopping sigma-field

Protter III.5 is proved for finite stopping times using actual predictable
evaluation. For arbitrary stopping times the identity uses our explicit terminal
owner and terminal-field-measurable inputs. The terminal data must not be erased:
at an identically infinite time, zero-terminal samples would all be zero, whereas
the pre-stopping field is the entire terminal filtration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {τ : Ω → WithTop ℝ≥0}

theorem measurableSpaceBefore_eq_iSup_comap_predictable_terminal
    (hτ : IsStoppingTime F τ) :
    hτ.measurableSpaceBefore =
      ⨆ (X : ℝ≥0 → Ω → ℝ) (_ : IsStronglyPredictable F X)
        (Z : Ω → ℝ) (_ : StronglyMeasurable[⨆ t, F t] Z),
        MeasurableSpace.comap (stoppedValueWithTerminal X Z τ) inferInstance := by
  classical
  let C := ⨆ (X : ℝ≥0 → Ω → ℝ) (_ : IsStronglyPredictable F X)
      (Z : Ω → ℝ) (_ : StronglyMeasurable[⨆ t, F t] Z),
      MeasurableSpace.comap (stoppedValueWithTerminal X Z τ) inferInstance
  change hτ.measurableSpaceBefore = C
  have hgen (X : ℝ≥0 → Ω → ℝ) (hX : IsStronglyPredictable F X)
      (Z : Ω → ℝ) (hZ : StronglyMeasurable[⨆ t, F t] Z) :
      Measurable[C] (stoppedValueWithTerminal X Z τ) :=
    measurable_iff_comap_le.mpr (le_iSup_of_le X (le_iSup_of_le hX
      (le_iSup_of_le Z (le_iSup_of_le hZ le_rfl))))
  apply le_antisymm
  · refine sup_le ?_ (MeasurableSpace.generateFrom_le ?_)
    · intro A hA
      let Z : Ω → ℝ := A.indicator (fun _ ↦ 1)
      let X : ℝ≥0 → Ω → ℝ := fun _ ↦ Z
      have ha : Adapted F X := fun t ↦ measurable_const.indicator (F.mono bot_le _ hA)
      have hp : IsStronglyPredictable F X :=
        ha.isStronglyPredictable_of_leftContinuous fun _ _ ↦ continuousWithinAt_const
      have hz : StronglyMeasurable[⨆ t, F t] Z :=
        (measurable_const.indicator (le_iSup F 0 _ hA)).stronglyMeasurable
      have hm := hgen X hp Z hz (measurableSet_singleton (1 : ℝ))
      convert hm using 1
      ext ω
      by_cases hω : ω ∈ A <;> simp [stoppedValueWithTerminal, stoppedValue, X, Z, hω]
    · rintro _ ⟨a, A, hA, rfl⟩
      let Z : Ω → ℝ := A.indicator (fun _ ↦ 1)
      let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ if a < t then Z ω else 0
      have ha : Adapted F X := by
        intro t
        by_cases ht : a < t
        · simp only [X, if_pos ht]
          exact measurable_const.indicator (F.mono ht.le _ hA)
        · simp only [X, if_neg ht]
          exact measurable_const
      have hp : IsStronglyPredictable F X :=
        ha.isStronglyPredictable_of_leftContinuous
          (fun ω ↦ (isCagladPath_step_Ioi a (Z ω)).1)
      have hz : StronglyMeasurable[⨆ t, F t] Z :=
        (measurable_const.indicator (le_iSup F a _ hA)).stronglyMeasurable
      have hm := hgen X hp Z hz (measurableSet_singleton (1 : ℝ))
      convert hm using 1
      ext ω
      change (ω ∈ A ∧ (a : WithTop ℝ≥0) < τ ω) ↔
        stoppedValueWithTerminal X Z τ ω = 1
      cases ht : τ ω with
      | top =>
        rw [stoppedValueWithTerminal_of_top ht]
        constructor
        · intro hω
          simp [Z, hω.1]
        · intro hω
          exact ⟨by simpa [Z] using hω, WithTop.coe_lt_top a⟩
      | coe t =>
        have hv : stoppedValueWithTerminal X Z τ ω = X t ω := by
          rw [stoppedValueWithTerminal_of_ne_top (ht ▸ WithTop.coe_ne_top)]
          change X ((τ ω).untopA) ω = X t ω
          rw [ht]
          rfl
        rw [hv, WithTop.coe_lt_coe]
        by_cases ha : a < t <;> simp [X, Z, ha]
  · refine iSup_le fun X ↦ iSup_le fun hX ↦ iSup_le fun Z ↦ iSup_le fun hZ ↦ ?_
    exact (hX.stronglyMeasurable_stoppedValueWithTerminal_before hZ hτ).measurable.comap_le

end MeasureTheory.IsStoppingTime

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- Protter III.5: finite predictable evaluations generate exactly `F_{T-}`. -/
theorem measurableSpaceBefore_eq_iSup_comap_predictable (τ : FiniteStoppingTime F) :
    τ.isStoppingTime.measurableSpaceBefore =
      ⨆ (X : ℝ≥0 → Ω → ℝ) (_ : IsStronglyPredictable F X),
        MeasurableSpace.comap (fun ω ↦ X (τ ω) ω) inferInstance := by
  apply le_antisymm
  · rw [τ.isStoppingTime.measurableSpaceBefore_eq_iSup_comap_predictable_terminal]
    refine iSup_le fun X ↦ iSup_le fun hX ↦ iSup_le fun Z ↦ iSup_le fun _ ↦ ?_
    rw [MeasureTheory.stoppedValueWithTerminal_coe]
    exact le_iSup_of_le X (le_iSup_of_le hX le_rfl)
  · refine iSup_le fun X ↦ iSup_le fun hX ↦ ?_
    exact (hX.stronglyMeasurable_finiteStoppingTime_before τ).measurable.comap_le

end ProbabilityTheory.FiniteStoppingTime
