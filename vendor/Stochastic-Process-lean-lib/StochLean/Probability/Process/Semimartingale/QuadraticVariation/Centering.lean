/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Constants
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Algebra
public import StochLean.Probability.Process.Semimartingale.Subtraction

/-! # Centering the raw square bracket

Subtracting the arbitrary initial random variable subtracts exactly its square
from the raw bracket. No integrability or zero-initial assumption is added.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem quadraticVariation_const_initial (hZ : Measurable[F 0] Z) (hF : F.IsUsual P) :
    Indistinguishable ((isSemimartingale_const_initial hZ).quadraticVariation hF)
      (fun _ ω ↦ (Z ω) ^ 2) P := by
  let hC := isSemimartingale_const_initial (P := P) hZ
  filter_upwards [hC.quadraticCovariation_self hF,
    hC.quadraticCovariation_const_initial_left hZ hF] with ω hs hc t
  rw [← hs t, hc t, pow_two]

theorem IsSemimartingale.quadraticVariation_sub_initial
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable
      ((hX.sub (isSemimartingale_const_initial (hX.adapted 0))).quadraticVariation hF)
      (fun t ω ↦ hX.quadraticVariation hF t ω - (X 0 ω) ^ 2) P := by
  let hC := isSemimartingale_const_initial (P := P) (hX.adapted 0)
  have heq : Indistinguishable (X + (fun _ ω ↦ (-1 : ℝ) * X 0 ω))
      (X - (fun _ ↦ X 0)) P := by
    apply ae_of_all
    intro ω t
    simp only [Pi.add_apply, Pi.sub_apply, neg_one_mul, sub_eq_add_neg]
  have hcongr := (hX.add (hC.const_mul (-1))).quadraticVariation_congr (hX.sub hC) hF heq
  filter_upwards [hX.quadraticVariation_add_const_mul hC hF (-1), hcongr,
    hX.quadraticCovariation_const_initial_right (hX.adapted 0) hF,
    quadraticVariation_const_initial (hX.adapted 0) hF] with ω ha he hc hq t
  rw [← he t, ha t, hc t, hq t]
  ring

end ProbabilityTheory
