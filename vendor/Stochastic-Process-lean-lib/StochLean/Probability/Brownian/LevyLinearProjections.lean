/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.FiniteLinearCombination
public import StochLean.Probability.Process.LocalMartingale.DeterministicBracketLaw
public import
  StochLean.Probability.Process.Semimartingale.QuadraticVariation.FiniteLinearCombination

/-! # Gaussian linear projections of orthogonal continuous local martingales

The projection is an actual finite linear combination and its bracket is
computed from the existing coordinate brackets. These projection results
are prerequisites for, not a substitute for, joint process independence.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ι → ℝ≥0 → Ω → ℝ}

theorem hasLaw_gaussian_linearCombination_increment_of_orthogonal
    (S : Finset ι) (hX : ∀ i, IsContinuousLocalMartingale (X i) F P)
    (hF : F.IsUsual P) (a : ι → ℝ)
    (hd : ∀ i, Indistinguishable ((hX i).isSemimartingale hF |>.continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ∑ i ∈ S, a i * (X i t ω - X i s ω))
      (gaussianReal 0 (Real.toNNReal ((∑ i ∈ S, a i ^ 2) * ((t : ℝ) - s)))) P := by
  let hL := isContinuousLocalMartingale_finset_linearCombination S hF a (fun i _ ↦ hX i)
  have hq := continuousQuadraticVariation_linearCombination_of_orthogonal S
    (fun i ↦ (hX i).isSemimartingale hF) hF a hd ho
  have h := hL.hasLaw_gaussian_increment_of_deterministic_bracket hF hq hst
  change HasLaw
    (fun ω ↦ (∑ i ∈ S, a i * X i t ω) - (∑ i ∈ S, a i * X i s ω))
    (gaussianReal 0 (Real.toNNReal
      ((∑ i ∈ S, a i ^ 2) * (t : ℝ) - (∑ i ∈ S, a i ^ 2) * (s : ℝ)))) P at h
  rw [← mul_sub] at h
  apply h.congr
  apply Filter.Eventually.of_forall
  intro ω
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem condExp_characteristic_linearCombination_of_orthogonal
    (S : Finset ι) (hX : ∀ i, IsContinuousLocalMartingale (X i) F P)
    (hF : F.IsUsual P) (a : ι → ℝ)
    (hd : ∀ i, Indistinguishable ((hX i).isSemimartingale hF |>.continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ Complex.exp (Complex.I * Complex.ofReal
      (∑ i ∈ S, a i * (X i t ω - X i s ω))) | F s] =ᵐ[P]
      fun _ ↦ Complex.exp (Complex.ofReal
        (-((1 / 2 : ℝ) * (∑ i ∈ S, a i ^ 2)) * ((t : ℝ) - s))) := by
  let hL := isContinuousLocalMartingale_finset_linearCombination S hF a (fun i _ ↦ hX i)
  have hq := continuousQuadraticVariation_linearCombination_of_orthogonal S
    (fun i ↦ (hX i).isSemimartingale hF) hF a hd ho
  have h := hL.condExp_characteristic_increment_of_deterministic_bracket hF hq hst 1
  have he : -((1 / 2 : ℝ) * 1 ^ 2) *
      ((∑ i ∈ S, a i ^ 2) * (t : ℝ) - (∑ i ∈ S, a i ^ 2) * (s : ℝ)) =
        -((1 / 2 : ℝ) * (∑ i ∈ S, a i ^ 2)) * ((t : ℝ) - s) := by ring
  simpa only [he, hL, mul_sub, Finset.sum_sub_distrib, Complex.ofReal_one, mul_one] using h

end ProbabilityTheory
