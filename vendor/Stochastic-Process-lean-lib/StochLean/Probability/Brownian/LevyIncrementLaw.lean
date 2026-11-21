/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.LevyConditionalCharacteristic
public import StochLean.Probability.Independence.ConditionalCharacteristic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian increments and past independence in Levy's characterization

The increment law and independence follow from the proved conditional
characteristic function, including the degenerate zero-length interval.
No zero initial value is needed for these increment statements.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.condExp_increment_eq_gaussian_charFun
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * ((X t ω - X s ω : ℝ) : ℂ)) | F s] =ᵐ[P]
      fun _ ↦ charFun (gaussianReal 0 (t - s)) u := by
  have he : Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) *
      ((t : ℝ) - (s : ℝ)))) = charFun (gaussianReal 0 (t - s)) u := by
    rw [charFun_gaussianReal]
    congr 1
    simp only [NNReal.coe_sub hst, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
    ring
  exact (hM.condExp_characteristic_increment hF hq hst u).trans
    (Filter.Eventually.of_forall (fun _ ↦ he))

theorem IsContinuousLocalMartingale.hasLaw_gaussian_increment_of_bracket_eq_time
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ X t ω - X s ω) (gaussianReal 0 (t - s)) P := by
  apply hasLaw_of_condExp_characteristic (F.le s)
    (((hM.isSemimartingale hF).adapted.measurable (i := t)).sub
      ((hM.isSemimartingale hF).adapted.measurable (i := s)))
  exact hM.condExp_increment_eq_gaussian_charFun hF hq hst

theorem IsContinuousLocalMartingale.indep_increment_past_of_bracket_eq_time
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (F s) (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P := by
  apply indep_comap_of_condExp_characteristic (ν := gaussianReal 0 (t - s)) (F.le s)
    (((hM.isSemimartingale hF).adapted.measurable (i := t)).sub
      ((hM.isSemimartingale hF).adapted.measurable (i := s)))
  exact hM.condExp_increment_eq_gaussian_charFun hF hq hst

end ProbabilityTheory
