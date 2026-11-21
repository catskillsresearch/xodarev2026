/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.ForMathlib.MeasureTheory.Function.ConvergenceInMeasureMixture

/-! # Protter II.3: countable mixtures of measures

The more general finite-total-mass sum result is proved first. The probability-mixture
version includes zero weights and does not impose uniform convergence rates on components.
Filtration usualness under the component or mixture measures is not needed here.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem IsGoodIntegrator.smul_measure (hX : IsGoodIntegrator X F P) (c : ℝ≥0) :
    IsGoodIntegrator X F ((c : ℝ≥0∞) • P) :=
  fun H hH hu ↦ (hX H hH hu).smul_measure c

theorem IsTotalSemimartingale.smul_measure (hX : IsTotalSemimartingale X F P) (c : ℝ≥0) :
    IsTotalSemimartingale X F ((c : ℝ≥0∞) • P) :=
  ⟨hX.1, Measure.ae_smul_measure hX.2.1 _, hX.2.2.smul_measure c⟩

theorem IsSemimartingale.smul_measure (hX : IsSemimartingale X F P) (c : ℝ≥0) :
    IsSemimartingale X F ((c : ℝ≥0∞) • P) :=
  fun T ↦ (hX T).smul_measure c

theorem isGoodIntegrator_sum_measure {μ : ℕ → Measure Ω}
    (hfinite : (∑' k, μ k univ) ≠ ∞) (hX : ∀ k, IsGoodIntegrator X F (μ k)) :
    IsGoodIntegrator X F (Measure.sum μ) :=
  fun H hH hu ↦ tendstoInMeasure_sum hfinite (fun k ↦ hX k H hH hu)

theorem isTotalSemimartingale_sum_measure {μ : ℕ → Measure Ω}
    (hfinite : (∑' k, μ k univ) ≠ ∞) (hX : ∀ k, IsTotalSemimartingale X F (μ k)) :
    IsTotalSemimartingale X F (Measure.sum μ) :=
  ⟨(hX 0).1, Measure.ae_sum_iff.mpr (fun k ↦ (hX k).2.1),
    isGoodIntegrator_sum_measure hfinite (fun k ↦ (hX k).2.2)⟩

theorem isSemimartingale_sum_measure {μ : ℕ → Measure Ω}
    (hfinite : (∑' k, μ k univ) ≠ ∞) (hX : ∀ k, IsSemimartingale X F (μ k)) :
    IsSemimartingale X F (Measure.sum μ) :=
  fun T ↦ isTotalSemimartingale_sum_measure hfinite (fun k ↦ hX k T)

/-- Protter II.3, including zero coefficients. -/
theorem isSemimartingale_probability_mixture (P : ℕ → Measure Ω)
    [∀ k, IsProbabilityMeasure (P k)] (c : ℕ → ℝ≥0)
    (hc : (∑' k, (c k : ℝ≥0∞)) = 1) (hX : ∀ k, IsSemimartingale X F (P k)) :
    IsSemimartingale X F (Measure.sum (fun k ↦ (c k : ℝ≥0∞) • P k)) := by
  apply isSemimartingale_sum_measure
  · simpa only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, hc] using
      (ENNReal.one_ne_top : (1 : ℝ≥0∞) ≠ ∞)
  · exact fun k ↦ (hX k).smul_measure (c k)

end ProbabilityTheory
