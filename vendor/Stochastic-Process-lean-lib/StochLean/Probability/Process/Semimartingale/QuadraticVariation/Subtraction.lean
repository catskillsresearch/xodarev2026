/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Algebra
public import StochLean.Probability.Process.Semimartingale.Subtraction

/-! # Subtraction for the canonical raw square bracket -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticVariation_sub
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.sub hY).quadraticVariation hF)
      (fun t ω ↦ hX.quadraticVariation hF t ω -
        2 * hX.quadraticCovariation hY hF t ω + hY.quadraticVariation hF t ω) P := by
  have he : Indistinguishable (X + (fun t ω ↦ (-1 : ℝ) * Y t ω)) (X - Y) P := by
    apply ae_of_all
    intro ω t
    simp only [Pi.add_apply, Pi.sub_apply, neg_one_mul, sub_eq_add_neg]
  filter_upwards [hX.quadraticVariation_add_const_mul hY hF (-1),
    (hX.add (hY.const_mul (-1))).quadraticVariation_congr (hX.sub hY) hF he]
    with ω ha heω t
  rw [← heω t, ha t]
  ring

end ProbabilityTheory
