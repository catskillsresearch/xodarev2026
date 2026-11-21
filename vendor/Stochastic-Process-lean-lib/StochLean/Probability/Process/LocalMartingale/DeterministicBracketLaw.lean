/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticExponential.DeterministicBracket
public import StochLean.Probability.Independence.ConditionalCharacteristic
public import StochLean.Probability.Process.IndependentIncrements.Filtration
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian increments from a deterministic continuous bracket

The clock's monotonicity is a consequence of its identification with the
canonical bracket. Flat clock intervals give a Dirac increment law. Initial
random shifts are unrestricted and do not enter the variance of increments.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {q : ℝ≥0 → ℝ}

theorem IsContinuousLocalMartingale.monotone_deterministic_bracket
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ q t) P) : Monotone q := by
  obtain ⟨ω, hω⟩ := Filter.Eventually.exists hq
  change ∀ r, (hM.isSemimartingale hF).continuousQuadraticVariation hF r ω = q r at hω
  intro s t hst
  rw [← hω s, ← hω t]
  exact (hM.isSemimartingale hF).monotone_continuousQuadraticVariation hF ω hst

theorem IsContinuousLocalMartingale.condExp_gaussian_charFun_of_deterministic_bracket
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ q t) P) {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * ((X t ω - X s ω : ℝ) : ℂ)) | F s] =ᵐ[P]
      fun _ ↦ charFun (gaussianReal 0 (Real.toNNReal (q t - q s))) u := by
  have hnonneg : 0 ≤ q t - q s := sub_nonneg.mpr
    (hM.monotone_deterministic_bracket hF hq hst)
  have he : Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) * (q t - q s))) =
      charFun (gaussianReal 0 (Real.toNNReal (q t - q s))) u := by
    rw [charFun_gaussianReal]
    congr 1
    simp only [Real.coe_toNNReal _ hnonneg, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
    ring
  exact (hM.condExp_characteristic_increment_of_deterministic_bracket hF hq hst u).trans
    (Filter.Eventually.of_forall (fun _ ↦ he))

theorem IsContinuousLocalMartingale.hasLaw_gaussian_increment_of_deterministic_bracket
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ q t) P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ X t ω - X s ω) (gaussianReal 0 (Real.toNNReal (q t - q s))) P := by
  apply hasLaw_of_condExp_characteristic (F.le s)
    (((hM.isSemimartingale hF).adapted.measurable (i := t)).sub
      ((hM.isSemimartingale hF).adapted.measurable (i := s)))
  exact hM.condExp_gaussian_charFun_of_deterministic_bracket hF hq hst

theorem IsContinuousLocalMartingale.indep_increment_past_of_deterministic_bracket
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ q t) P) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (F s) (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P := by
  apply indep_comap_of_condExp_characteristic
    (ν := gaussianReal 0 (Real.toNNReal (q t - q s))) (F.le s)
    (((hM.isSemimartingale hF).adapted.measurable (i := t)).sub
      ((hM.isSemimartingale hF).adapted.measurable (i := s)))
  exact hM.condExp_gaussian_charFun_of_deterministic_bracket hF hq hst

theorem IsContinuousLocalMartingale.hasIndepIncrements_of_deterministic_bracket
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ q t) P) : HasIndepIncrements X P :=
  (hM.isSemimartingale hF).adapted.hasIndepIncrements_of_indep_comap
    (fun _ _ hst ↦ hM.indep_increment_past_of_deterministic_bracket hF hq hst)

end ProbabilityTheory
