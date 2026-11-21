/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Independence.ConditionalCharacteristicHilbert

/-! # Constant conditional characteristic functions

Fourier uniqueness identifies the law restricted to every past event. In a
probability space this gives both the marginal law and independence from the
conditioning sigma-algebra, without a pre-existing distributional assumption.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

theorem map_restrict_eq_smul_of_condExp_characteristic
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hm : m ≤ mΩ) (hY : Measurable Y)
    (h : ∀ u : ℝ,
      P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * (Y ω : ℂ)) | m] =ᵐ[P]
        fun _ ↦ charFun ν u) {A : Set Ω} (hA : MeasurableSet[m] A) :
    (P.restrict A).map Y = P A • ν := by
  apply map_restrict_eq_smul_of_condExp_inner_characteristic hm hY ?_ hA
  intro u
  simpa [mul_comm, mul_left_comm, mul_assoc] using h u

theorem hasLaw_of_condExp_characteristic
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hm : m ≤ mΩ) (hY : Measurable Y)
    (h : ∀ u : ℝ,
      P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * (Y ω : ℂ)) | m] =ᵐ[P]
        fun _ ↦ charFun ν u) : HasLaw Y ν P := by
  refine ⟨hY.aemeasurable, ?_⟩
  simpa using map_restrict_eq_smul_of_condExp_characteristic hm hY h MeasurableSet.univ

theorem indep_comap_of_condExp_characteristic
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hm : m ≤ mΩ) (hY : Measurable Y)
    (h : ∀ u : ℝ,
      P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * (Y ω : ℂ)) | m] =ᵐ[P]
        fun _ ↦ charFun ν u) : Indep m (MeasurableSpace.comap Y inferInstance) P := by
  have hLaw := hasLaw_of_condExp_characteristic hm hY h
  apply (Indep_iff _ _ _).2
  intro A B hA hB
  obtain ⟨B, hB, rfl⟩ := hB
  have hr := congrArg (fun μ : Measure ℝ ↦ μ B)
    (map_restrict_eq_smul_of_condExp_characteristic hm hY h hA)
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB),
    Measure.smul_apply, smul_eq_mul] at hr
  rw [← hLaw.map_eq, Measure.map_apply hY hB] at hr
  simpa only [inter_comm] using hr

end ProbabilityTheory
