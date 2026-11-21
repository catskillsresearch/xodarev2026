/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic.Linarith

/-! # Conditional centering from joint sign symmetry

Equality of the joint laws of `(X,Y)` and `(-X,Y)` centers an integrable real variable
conditionally on `Y`. No independence hypothesis is required. In particular, `Y` may encode
an entire countable family of observables preserved by a path reflection.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace ProbabilityTheory

variable {Ω S : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace S}
  {P : Measure Ω} {X : Ω → ℝ} {Y : Ω → S}

theorem condExp_eq_zero_of_joint_neg [IsFiniteMeasure P]
    (hX : Integrable X P) (hY : Measurable Y)
    (hsym : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (-X ω, Y ω)) P P) :
    P[X | mS.comap Y] =ᵐ[P] 0 := by
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hY.comap_le hX
    (fun _ _ _ ↦ integrable_zero _ _ _) _ aestronglyMeasurable_zero
  intro s hs _
  obtain ⟨s', hs', rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hi := (hsym.comp (measurable_fst.indicator (measurable_snd hs'))).integral_eq
  change (∫ ω, (Y ⁻¹' s').indicator X ω ∂P) =
    ∫ ω, (Y ⁻¹' s').indicator (fun ω ↦ -X ω) ω ∂P at hi
  rw [integral_indicator (hY hs'), integral_indicator (hY hs'), integral_neg] at hi
  simp only [Pi.zero_apply, integral_zero]
  linarith

/-- Conditional orthogonality removes the off-diagonal terms in a finite square expansion. -/
theorem condExp_sq_sum_of_cross_zero {I : Type*} [Fintype I]
    (Z : I → Ω → ℝ) (hZ : ∀ i, MemLp (Z i) 2 P) (m : MeasurableSpace Ω)
    (hcross : ∀ i j, i ≠ j → P[Z i * Z j | m] =ᵐ[P] 0) :
    P[(fun ω ↦ (∑ i, Z i ω) ^ 2) | m] =ᵐ[P]
      ∑ i, P[(fun ω ↦ (Z i ω) ^ 2) | m] := by
  classical
  have hint (i j : I) : Integrable (Z i * Z j) P := (hZ i).integrable_mul (hZ j)
  have hrow (i : I) : P[∑ j, Z i * Z j | m] =ᵐ[P]
      P[(fun ω ↦ (Z i ω) ^ 2) | m] := by
    filter_upwards [condExp_finsetSum (s := Finset.univ) (fun j _ ↦ hint i j) m,
      ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (fun h : i ≠ j ↦ hcross i j h))]
      with ω hsum hz
    rw [hsum]
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · congr 1
      funext ω
      simp only [Pi.mul_apply, pow_two]
    · intro j _ hji
      exact hz j (Ne.symm hji)
    · simp
  have hsum := condExp_finsetSum (s := Finset.univ)
    (fun i _ ↦ integrable_finsetSum' Finset.univ (fun j _ ↦ hint i j)) m
  have heq : (fun ω ↦ (∑ i, Z i ω) ^ 2) = ∑ i, ∑ j, Z i * Z j := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, pow_two, Finset.sum_mul_sum]
  rw [heq]
  apply hsum.trans
  filter_upwards [ae_all_iff.mpr hrow] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ ↦ hω i)

end ProbabilityTheory
