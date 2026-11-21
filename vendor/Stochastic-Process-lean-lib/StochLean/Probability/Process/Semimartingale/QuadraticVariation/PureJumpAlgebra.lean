/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump

/-! # Linear stability of quadratic pure-jump semimartingales -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
  {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}

theorem IsSemimartingale.IsQuadraticPureJump.add
    (hx : hX.IsQuadraticPureJump hF) (hy : hY.IsQuadraticPureJump hF) :
    (hX.add hY).IsQuadraticPureJump hF := by
  filter_upwards [hX.continuousQuadraticVariation_add hY hF,
    hX.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hY hF hx, hx, hy]
    with ω ha hm hqx hqy t
  rw [ha t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm t, hqx t, hqy t,
    Pi.zero_apply, mul_zero, add_zero]

theorem IsSemimartingale.IsQuadraticPureJump.const_mul
    (hx : hX.IsQuadraticPureJump hF) (c : ℝ) :
    (hX.const_mul c).IsQuadraticPureJump hF := by
  filter_upwards [hX.continuousQuadraticVariation_const_mul hF c, hx] with ω he hz t
  rw [he t]
  simp only [Pi.smul_apply, smul_eq_mul, hz t, Pi.zero_apply, mul_zero]

theorem IsSemimartingale.IsQuadraticPureJump.neg
    (hx : hX.IsQuadraticPureJump hF) : hX.neg.IsQuadraticPureJump hF := by
  have he : Indistinguishable (fun t ω ↦ (-1 : ℝ) * X t ω) (-X) P :=
    ae_of_all _ fun ω t ↦ by simp
  exact (hx.const_mul (-1)).congr he

theorem IsSemimartingale.IsQuadraticPureJump.sub
    (hx : hX.IsQuadraticPureJump hF) (hy : hY.IsQuadraticPureJump hF) :
    (hX.sub hY).IsQuadraticPureJump hF := by
  have he : Indistinguishable (X + -Y) (X - Y) P :=
    ae_of_all _ fun ω t ↦ (sub_eq_add_neg _ _).symm
  exact (hx.add hy.neg).congr he

end ProbabilityTheory
