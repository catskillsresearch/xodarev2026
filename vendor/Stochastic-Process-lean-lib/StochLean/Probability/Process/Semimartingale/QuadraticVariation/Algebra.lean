/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Algebra

/-! # Quadratic identities for the canonical raw square bracket -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticVariation_add
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.add hY).quadraticVariation hF)
      (hX.quadraticVariation hF + (2 : ℝ) • hX.quadraticCovariation hY hF +
        hY.quadraticVariation hF) P := by
  apply ae_of_all
  intro ω t
  simp only [quadraticCovariation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem IsSemimartingale.quadraticVariation_const_mul
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable ((hX.const_mul c).quadraticVariation hF)
      ((c ^ 2) • hX.quadraticVariation hF) P := by
  filter_upwards [(hX.const_mul c).quadraticCovariation_self hF,
    hX.quadraticCovariation_const_mul_left (hX.const_mul c) hF c,
    hX.quadraticCovariation_const_mul_right hX hF c, hX.quadraticCovariation_self hF]
    with ω hself hleft hright hx t
  rw [← hself t, hleft t]
  simp only [Pi.smul_apply, smul_eq_mul, hright t, hx t]
  ring

theorem IsSemimartingale.quadraticVariation_add_const_mul
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable ((hX.add (hY.const_mul c)).quadraticVariation hF)
      (fun t ω ↦ hX.quadraticVariation hF t ω +
        2 * c * hX.quadraticCovariation hY hF t ω + c ^ 2 * hY.quadraticVariation hF t ω) P := by
  filter_upwards [hX.quadraticVariation_add (hY.const_mul c) hF,
    hX.quadraticCovariation_const_mul_right hY hF c, hY.quadraticVariation_const_mul hF c]
    with ω hadd hcross hsq t
  rw [hadd t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcross t, hsq t]
  ring

end ProbabilityTheory
