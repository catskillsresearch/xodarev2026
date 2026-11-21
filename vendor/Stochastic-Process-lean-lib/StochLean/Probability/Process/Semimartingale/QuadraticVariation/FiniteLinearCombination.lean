/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.FiniteSum

/-! # Continuous brackets of finite linear combinations

The full double sum precedes the orthogonal common-clock specialization.
Zero coefficients, an empty family and arbitrary initial values are retained.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ι → ℝ≥0 → Ω → ℝ}

theorem isSemimartingale_finset_linearCombination (S : Finset ι)
    (hX : ∀ i, IsSemimartingale (X i) F P) (a : ι → ℝ) :
    IsSemimartingale (fun t ω ↦ ∑ i ∈ S, a i * X i t ω) F P := by
  have h := isSemimartingale_finset_sum S (fun i ↦ (hX i).const_mul (a i))
  convert h using 1
  funext t ω
  simp only [Finset.sum_apply]

theorem continuousQuadraticVariation_finset_linearCombination (S : Finset ι)
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (a : ι → ℝ) :
    Indistinguishable
      ((isSemimartingale_finset_linearCombination S hX a).continuousQuadraticVariation hF)
      (fun t ω ↦ ∑ i ∈ S, ∑ j ∈ S,
        a i * a j * (hX i).continuousQuadraticCovariation (hX j) hF t ω) P := by
  let hA := fun i ↦ (hX i).const_mul (a i)
  have he : Indistinguishable (fun t ω ↦ ∑ i ∈ S, a i * X i t ω)
      (∑ i ∈ S, fun t ω ↦ a i * X i t ω) P := by
    apply Filter.Eventually.of_forall
    intro ω t
    simp only [Finset.sum_apply]
  have hp (i j : ι) : Indistinguishable
      ((hA i).continuousQuadraticCovariation (hA j) hF)
      (fun t ω ↦ a i * a j * (hX i).continuousQuadraticCovariation (hX j) hF t ω) P := by
    filter_upwards [(hX i).continuousQuadraticCovariation_const_mul_left (hA j) hF (a i),
      (hX i).continuousQuadraticCovariation_const_mul_right (hX j) hF (a j)] with ω hl hr t
    rw [hl t]
    simp only [Pi.smul_apply, smul_eq_mul, hr t]
    ring
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ S, ∀ j ∈ S, ∀ t,
      (hA i).continuousQuadraticCovariation (hA j) hF t ω =
        a i * a j * (hX i).continuousQuadraticCovariation (hX j) hF t ω :=
    (eventually_all_finset S).2 fun i _ ↦ (eventually_all_finset S).2 fun j _ ↦ hp i j
  filter_upwards [IsSemimartingale.continuousQuadraticVariation_congr
    (isSemimartingale_finset_linearCombination S hX a)
    (isSemimartingale_finset_sum S hA) hF he,
    continuousQuadraticVariation_finset_sum S hA hF, hall] with ω hcω hsω hpω t
  rw [hcω t, hsω t]
  exact Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ hpω i hi j hj t

theorem continuousQuadraticVariation_linearCombination_of_orthogonal (S : Finset ι)
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (a : ι → ℝ)
    {A : ℝ≥0 → Ω → ℝ}
    (hd : ∀ i, Indistinguishable ((hX i).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j →
      Indistinguishable ((hX i).continuousQuadraticCovariation (hX j) hF) 0 P) :
    Indistinguishable
      ((isSemimartingale_finset_linearCombination S hX a).continuousQuadraticVariation hF)
      (fun t ω ↦ (∑ i ∈ S, a i ^ 2) * A t ω) P := by
  classical
  have hp (i j : ι) : Indistinguishable
      ((hX i).continuousQuadraticCovariation (hX j) hF)
      (fun t ω ↦ if i = j then A t ω else 0) P := by
    by_cases hij : i = j
    · subst j
      simpa only [if_true] using ((hX i).continuousQuadraticCovariation_self hF).trans (hd i)
    · filter_upwards [ho i j hij] with ω hω t
      simpa only [if_neg hij, Pi.zero_apply] using hω t
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ S, ∀ j ∈ S, ∀ t,
      (hX i).continuousQuadraticCovariation (hX j) hF t ω =
        if i = j then A t ω else 0 :=
    (eventually_all_finset S).2 fun i _ ↦ (eventually_all_finset S).2 fun j _ ↦ hp i j
  filter_upwards [continuousQuadraticVariation_finset_linearCombination S hX hF a, hall]
    with ω hq hpω t
  rw [hq t, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [hpω i hi i hi t]
    simp only [if_true, pow_two]
  · intro j hj hji
    rw [hpω i hi j hj t, if_neg (Ne.symm hji), mul_zero]
  · intro hni
    exact False.elim (hni hi)

end ProbabilityTheory
