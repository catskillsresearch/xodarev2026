/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra

/-! # Quadratic algebra of the existing continuous square component -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticVariation_add
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.add hY).continuousQuadraticVariation hF)
      (hX.continuousQuadraticVariation hF +
        (2 : ℝ) • hX.continuousQuadraticCovariation hY hF +
        hY.continuousQuadraticVariation hF) P := by
  apply ae_of_all
  intro ω t
  simp only [continuousQuadraticCovariation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem IsSemimartingale.continuousQuadraticVariation_const_mul
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable ((hX.const_mul c).continuousQuadraticVariation hF)
      ((c ^ 2) • hX.continuousQuadraticVariation hF) P := by
  filter_upwards [(hX.const_mul c).continuousQuadraticCovariation_self hF,
    hX.continuousQuadraticCovariation_const_mul_left (hX.const_mul c) hF c,
    hX.continuousQuadraticCovariation_const_mul_right hX hF c,
    hX.continuousQuadraticCovariation_self hF] with ω hs hl hr hself t
  rw [← hs t, hl t]
  simp only [Pi.smul_apply, smul_eq_mul, hr t, hself t]
  ring

theorem IsSemimartingale.continuousQuadraticVariation_add_const_mul
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable ((hX.add (hY.const_mul c)).continuousQuadraticVariation hF)
      (fun t ω ↦ hX.continuousQuadraticVariation hF t ω +
        2 * c * hX.continuousQuadraticCovariation hY hF t ω +
        c ^ 2 * hY.continuousQuadraticVariation hF t ω) P := by
  filter_upwards [hX.continuousQuadraticVariation_add (hY.const_mul c) hF,
    hX.continuousQuadraticCovariation_const_mul_right hY hF c,
    hY.continuousQuadraticVariation_const_mul hF c] with ω ha hc hq t
  rw [ha t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc t, hq t]
  ring

end ProbabilityTheory
