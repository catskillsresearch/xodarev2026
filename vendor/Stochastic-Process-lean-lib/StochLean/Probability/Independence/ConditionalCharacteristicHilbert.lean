/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw

/-! # Conditional characteristic functions in real Hilbert spaces

Finite-measure Fourier uniqueness identifies every past-event restricted law.
The same identity yields the marginal law and independence from the entire
conditioning sigma-algebra. No conditional distribution or kernel is assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem map_restrict_eq_smul_of_condExp_inner_characteristic
    {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → E} {ν : Measure E} [IsFiniteMeasure ν]
    (hm : m ≤ mΩ) (hY : Measurable Y)
    (h : ∀ u : E,
      P[fun ω ↦ Complex.exp (Complex.ofReal ⟪Y ω, u⟫ * Complex.I) | m] =ᵐ[P]
        fun _ ↦ charFun ν u) {A : Set Ω} (hA : MeasurableSet[m] A) :
    (P.restrict A).map Y = P A • ν := by
  have : IsFiniteMeasure (P A • ν) := ν.smul_finite (measure_ne_top P A)
  apply Measure.ext_of_charFun
  funext u
  have hi : Integrable (fun ω ↦ Complex.exp (Complex.ofReal ⟪Y ω, u⟫ * Complex.I)) P :=
    (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  calc
    charFun ((P.restrict A).map Y) u =
        ∫ ω in A, Complex.exp (Complex.ofReal ⟪Y ω, u⟫ * Complex.I) ∂P := by
      rw [charFun_apply, integral_map hY.aemeasurable (by fun_prop)]
    _ = ∫ ω in A,
        P[fun ω ↦ Complex.exp (Complex.ofReal ⟪Y ω, u⟫ * Complex.I) | m] ω ∂P :=
      (setIntegral_condExp hm hi hA).symm
    _ = ∫ _ in A, charFun ν u ∂P := integral_congr_ae (ae_restrict_of_ae (h u))
    _ = (P A).toReal • charFun ν u := by rw [setIntegral_const]; rfl
    _ = charFun (P A • ν) u := by simp only [charFun_apply, integral_smul_measure]

theorem hasLaw_of_condExp_inner_characteristic
    {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → E} {ν : Measure E} [IsFiniteMeasure ν]
    (hm : m ≤ mΩ) (hY : Measurable Y)
    (h : ∀ u : E,
      P[fun ω ↦ Complex.exp (Complex.ofReal ⟪Y ω, u⟫ * Complex.I) | m] =ᵐ[P]
        fun _ ↦ charFun ν u) : HasLaw Y ν P := by
  refine ⟨hY.aemeasurable, ?_⟩
  simpa using map_restrict_eq_smul_of_condExp_inner_characteristic hm hY h MeasurableSet.univ

theorem indep_comap_of_condExp_inner_characteristic
    {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → E} {ν : Measure E} [IsFiniteMeasure ν]
    (hm : m ≤ mΩ) (hY : Measurable Y)
    (h : ∀ u : E,
      P[fun ω ↦ Complex.exp (Complex.ofReal ⟪Y ω, u⟫ * Complex.I) | m] =ᵐ[P]
        fun _ ↦ charFun ν u) : Indep m (MeasurableSpace.comap Y inferInstance) P := by
  have hLaw := hasLaw_of_condExp_inner_characteristic hm hY h
  apply (Indep_iff _ _ _).2
  intro A B hA hB
  obtain ⟨B, hB, rfl⟩ := hB
  have hr := congrArg (fun μ : Measure E ↦ μ B)
    (map_restrict_eq_smul_of_condExp_inner_characteristic hm hY h hA)
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB),
    Measure.smul_apply, smul_eq_mul] at hr
  rw [← hLaw.map_eq, Measure.map_apply hY hB] at hr
  simpa only [inter_comm] using hr

end ProbabilityTheory
