/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.RightContinuousAugmentation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Actual conditional expectation under usual augmentation

Null-set enlargement preserves conditional expectations of original L1
random variables. The ambient space and measure are genuinely completed.
Original integrability and integrals are transported using the actual trim
of the completed measure, not by identifying the two ambient sigma-fields.

For an already right-continuous filtration, the preceding augmentation
theorem then gives the actual usual-augmentation conditional expectation.
-/

@[expose] public section

open Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

private theorem le_completion_space :
    mΩ ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
  fun _ hs ↦ hs.nullMeasurableSet

private theorem completion_trim_original :
    P.completion.trim (le_completion_space (P := P)) = P := by
  apply @Measure.ext Ω mΩ
  intro s hs
  exact (trim_measurableSet_eq (μ := P.completion)
    (le_completion_space (P := P)) hs).trans rfl

private theorem integrable_on_completion {Y : Ω → ℝ} (hY : Integrable Y P) :
    Integrable (fun ω : NullMeasurableSpace Ω P ↦ Y ω) P.completion := by
  apply integrable_of_integrable_trim (le_completion_space (P := P))
  exact (congrArg (fun μ : @Measure Ω mΩ ↦ Integrable Y μ)
    (completion_trim_original (P := P))).mpr hY

private theorem integral_on_completion {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) :
    (∫ ω : NullMeasurableSpace Ω P, Y ω ∂P.completion) = ∫ ω, Y ω ∂P := by
  have hY' : AEStronglyMeasurable Y
      (P.completion.trim (le_completion_space (P := P))) :=
    (congrArg (fun μ : @Measure Ω mΩ ↦ AEStronglyMeasurable Y μ)
      (completion_trim_original (P := P))).mpr hY
  exact (integral_trim_ae (le_completion_space (P := P)) hY').trans
    (congrArg (fun μ : @Measure Ω mΩ ↦ ∫ ω, Y ω ∂μ)
      (completion_trim_original (P := P)))

private theorem setIntegral_on_completion {Y : Ω → ℝ}
    (hY : AEStronglyMeasurable Y P) {s : Set Ω} (hs : MeasurableSet s) :
    (∫ ω : NullMeasurableSpace Ω P in s, Y ω ∂P.completion) = ∫ ω in s, Y ω ∂P := by
  exact (integral_indicator (μ := P.completion)
    (le_completion_space (P := P) _ hs)).symm.trans
      ((integral_on_completion (hY.indicator hs)).trans (integral_indicator hs))

/-- The actual conditional expectation after adjoining ambient null sets
and completing the ambient space agrees almost surely with the original
conditional expectation. -/
theorem condExp_sup_nullSets_completion [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {Y : Ω → ℝ} (hY : Integrable Y P) :
    P.completion[(fun ω : NullMeasurableSpace Ω P ↦ Y ω) |
      m ⊔ @Filtration.nullSets Ω mΩ P] =ᵐ[P.completion] P[Y | m] := by
  let H := P[Y | m]
  have hm' : m ⊔ @Filtration.nullSets Ω mΩ P ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) := by
    refine sup_le (hm.trans (le_completion_space (P := P))) ?_
    exact MeasurableSpace.generateFrom_le fun s hs ↦ NullMeasurableSet.of_null hs
  let μC : @Measure Ω (eventuallyMeasurableSpace mΩ (ae P)) := P.completion
  have hiH : Integrable H P := integrable_condExp
  have hiH' : Integrable (fun ω : NullMeasurableSpace Ω P ↦ H ω) P.completion :=
    integrable_on_completion hiH
  have hmH : StronglyMeasurable[m ⊔ @Filtration.nullSets Ω mΩ P] H :=
    (show StronglyMeasurable[m] H from stronglyMeasurable_condExp).mono le_sup_left
  let : IsFiniteMeasure (μC.trim hm') := ⟨by
    exact (trim_measurableSet_eq hm' MeasurableSet.univ).trans_lt
      (show P.completion univ < ∞ from measure_lt_top P univ)⟩
  change μC[Y | m ⊔ @Filtration.nullSets Ω mΩ P] =ᵐ[μC] H
  apply EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (α := Ω)
    (m₀ := eventuallyMeasurableSpace mΩ (ae P))
    (μ := μC) hm' (integrable_on_completion hY)
    (fun _ _ _ ↦ hiH'.integrableOn) ?_ hmH.aestronglyMeasurable
  intro E hE _
  obtain ⟨B, hB, he⟩ := ProbabilityTheory.exists_measurable_ae_eq_of_sup_nullSets hE
  have he' : E =ᵐ[P.completion] B := he
  calc
    (∫ ω : NullMeasurableSpace Ω P in E, H ω ∂P.completion) =
        ∫ ω : NullMeasurableSpace Ω P in B, H ω ∂P.completion := setIntegral_congr_set he'
    _ = ∫ ω in B, H ω ∂P := setIntegral_on_completion hiH.aestronglyMeasurable (hm _ hB)
    _ = ∫ ω in B, Y ω ∂P := setIntegral_condExp hm hY hB
    _ = ∫ ω : NullMeasurableSpace Ω P in B, Y ω ∂P.completion :=
      (setIntegral_on_completion hY.aestronglyMeasurable (hm _ hB)).symm
    _ = ∫ ω : NullMeasurableSpace Ω P in E, Y ω ∂P.completion :=
      setIntegral_congr_set he'.symm

/-- An already right-continuous raw filtration has the same actual L1
conditional expectations as its genuine usual augmentation. -/
theorem Filtration.condExp_usualAugmentation_of_isRightContinuous
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (hF : F.IsRightContinuous) {Y : Ω → ℝ} (hY : Integrable Y P) (t : ℝ≥0) :
    P.completion[(fun ω : NullMeasurableSpace Ω P ↦ Y ω) |
      F.usualAugmentation P t] =ᵐ[P.completion] P[Y | F t] := by
  rw [Filtration.usualAugmentation_eq_withNullSets hF]
  exact condExp_sup_nullSets_completion (F.le t) hY

end MeasureTheory
