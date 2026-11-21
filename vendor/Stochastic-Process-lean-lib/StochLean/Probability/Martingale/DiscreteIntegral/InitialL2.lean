/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.DiscreteIntegral.L2

/-! # L2 estimates retaining the initial term

An initial, time-zero measurable square-integrable value is orthogonal to the future
predictable integral. The resulting estimate includes the source initial contribution.
-/

@[expose] public section

open Filter Finset
open scoped NNReal ENNReal BigOperators

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem Martingale.integral_pathwiseQuadraticVariation_eq_integral_sq_sub_initial_sq
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P) (n : ℕ) :
    ∫ ω, pathwiseQuadraticVariation M n ω ∂P =
      (∫ ω, (M n ω) ^ 2 ∂P) - ∫ ω, (M 0 ω) ^ 2 ∂P := by
  have heq := (hM.square_sub_pathwiseQuadraticVariation hlp).setIntegral_eq
    (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, squareMinusPathwiseQuadraticVariation,
    pathwiseQuadraticVariation_zero, sub_zero] at heq
  change (∫ ω, (M 0 ω) ^ 2 ∂P) = ∫ ω, (M n ω) ^ 2 - pathwiseQuadraticVariation M n ω ∂P at heq
  rw [integral_sub (hlp n).integrable_sq
    (integrable_pathwiseQuadraticVariation
      (fun k ↦ ((hlp (k + 1)).sub (hlp k)).integrable_sq) n)] at heq
  linarith

theorem Martingale.integral_sq_initial_add_discreteStochasticIntegral
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P)
    (hH : IsStronglyPredictable F H) (hb : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[F 0] Z) (hZlp : MemLp Z 2 P) (n : ℕ) :
    ∫ ω, (Z ω + MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P =
      (∫ ω, (Z ω) ^ 2 ∂P) + ∫ ω, (MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P := by
  let I := MeasureTheory.discreteStochasticIntegral H M
  have hI : Martingale I F P := hM.discreteStochasticIntegral hH hb
  have hIlp : ∀ n, MemLp (I n) 2 P := memLp_discreteStochasticIntegral hlp hH hb
  let N : ℕ → Ω → ℝ := fun n ω ↦ Z ω + I n ω
  have hN : Martingale N F P :=
    (martingale_const_fun F P hZ (hZlp.integrable (by norm_num))).add hI
  have hNlp : ∀ n, MemLp (N n) 2 P := fun n ↦ hZlp.add (hIlp n)
  have hQV : pathwiseQuadraticVariation N n = pathwiseQuadraticVariation I n := by
    funext ω
    apply sum_congr rfl
    intro k _
    change ((Z ω + I (k + 1) ω) - (Z ω + I k ω)) ^ 2 = _
    rw [add_sub_add_left_eq_sub]
  have heq := hN.integral_pathwiseQuadraticVariation_eq_integral_sq_sub_initial_sq hNlp n
  rw [hQV, hI.integral_pathwiseQuadraticVariation_eq_integral_sq_sub_initial_sq hIlp n] at heq
  have hI0 : I 0 = 0 := discreteStochasticIntegral_zero H M
  have hN0 : N 0 = Z := by simp only [N, hI0, Pi.zero_apply, add_zero]
  rw [hI0, hN0] at heq
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integral_zero, sub_zero] at heq
  change _ = (∫ ω, (Z ω + I n ω) ^ 2 ∂P) - _ at heq
  linarith

theorem Martingale.integral_sq_initial_add_discreteStochasticIntegral_le
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P)
    (hH : IsStronglyPredictable F H) (C : ℝ≥0)
    (hb : ∀ n, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[F 0] Z) (hZlp : MemLp Z 2 P)
    (hZb : ∀ᵐ ω ∂P, (Z ω) ^ 2 ≤ (C : ℝ) ^ 2 * (M 0 ω) ^ 2) (n : ℕ) :
    ∫ ω, (Z ω + MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (M n ω) ^ 2 ∂P := by
  rw [hM.integral_sq_initial_add_discreteStochasticIntegral hlp hH
    (fun k ↦ ⟨C, hb k⟩) hZ hZlp]
  have hZi : (∫ ω, (Z ω) ^ 2 ∂P) ≤ (C : ℝ) ^ 2 * ∫ ω, (M 0 ω) ^ 2 ∂P := by
    rw [← integral_const_mul]
    exact integral_mono_ae hZlp.integrable_sq ((hlp 0).integrable_sq.const_mul _) hZb
  have hIi := hM.integral_sq_discreteStochasticIntegral_le hlp hH C hb n
  have heq := hM.integral_pathwiseQuadraticVariation_eq_integral_sub_initial_sq hlp n
  rw [hM.integral_pathwiseQuadraticVariation_eq_integral_sq_sub_initial_sq hlp n] at heq
  rw [← heq] at hIi
  nlinarith

end MeasureTheory
