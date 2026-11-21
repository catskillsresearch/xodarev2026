/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Centering
public import StochLean.Probability.Martingale.MonotonePaths

/-! # The increasing-sign convention in discrete Doob decomposition

For a supermartingale, the increasing term is Mathlib's predictable part
of the negative process, and the martingale term is the negative martingale
part of that same process. No second selected decomposition is introduced.
-/

@[expose] public section

open ProbabilityTheory Filter

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}

theorem doob_decomposition_data (hX : Supermartingale X F P) :
    let A := predictablePart (-X) F P
    let M := -martingalePart (-X) F P
    Martingale M F P ∧ IsStronglyPredictable F A ∧ A 0 = 0 ∧ M 0 = X 0 ∧
      M - A = X ∧ HasMonotonePaths A P ∧
      (∀ᵐ ω ∂P, ∀ n, 0 ≤ A n ω) ∧ (∀ n, Integrable (A n) P) ∧
      ∀ n, (∫ ω, A n ω ∂P) = (∫ ω, X 0 ω ∂P) - ∫ ω, X n ω ∂P := by
  intro A M
  have hM : Martingale M F P :=
    (martingale_martingalePart hX.neg.stronglyAdapted hX.neg.integrable).neg
  have hA : IsStronglyPredictable F A := isPredictable_predictablePart
  have hA0 : A 0 = 0 := predictablePart_zero
  have hM0 : M 0 = X 0 := by simp only [M, Pi.neg_apply, martingalePart_zero, neg_neg]
  have he : M - A = X := by
    funext n ω
    change -(-X n ω - A n ω) - A n ω = X n ω
    ring
  have hiA (n : ℕ) : Integrable (A n) P := by
    dsimp only [A, predictablePart]
    fun_prop
  refine ⟨hM, hA, hA0, hM0, he, hX.neg.monotone_predictablePart,
    hX.neg.predictablePart_nonneg, hiA, fun n ↦ ?_⟩
  have heM : M n = X n + A n := by
    funext ω
    have h := congrFun (congrFun he n) ω
    change M n ω - A n ω = X n ω at h
    change M n ω = X n ω + A n ω
    linarith
  have hi := hM.setIntegral_eq (Nat.zero_le n) (@MeasurableSet.univ Ω (F 0))
  rw [setIntegral_univ, setIntegral_univ, hM0, heM] at hi
  change (∫ ω, X 0 ω ∂P) = ∫ ω, X n ω + A n ω ∂P at hi
  rw [integral_add (hX.integrable n) (hiA n)] at hi
  linarith

end MeasureTheory.Supermartingale
