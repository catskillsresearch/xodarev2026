/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump

/-! # Finite-variation perturbations do not change the continuous square bracket

The perturbation may jump; only its continuous quadratic variation vanishes.
These identities do not assert the corresponding claim for the raw bracket.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X A : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticVariation_add_const_mul_finiteVariation
    (hX : IsSemimartingale X F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths A P) (c : ℝ) :
    Indistinguishable ((hX.add (hA.const_mul c)).continuousQuadraticVariation hF)
      (hX.continuousQuadraticVariation hF) P := by
  have hQ := hA.isQuadraticPureJump_of_finiteVariation hF hv
  filter_upwards [hX.continuousQuadraticVariation_add_const_mul hA hF c,
    hX.continuousQuadraticCovariation_zero_of_quadraticPureJump_right hA hF hQ, hQ]
      with ω hi hm hz t
  simpa only [hm t, hz t, Pi.zero_apply, mul_zero, add_zero] using hi t

theorem IsSemimartingale.continuousQuadraticVariation_add_finiteVariation
    (hX : IsSemimartingale X F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths A P) :
    Indistinguishable ((hX.add hA).continuousQuadraticVariation hF)
      (hX.continuousQuadraticVariation hF) P := by
  have he : Indistinguishable (X + A) (X + fun t ω ↦ (1 : ℝ) * A t ω) P :=
    Filter.Eventually.of_forall (fun _ _ ↦ by simp only [Pi.add_apply, one_mul])
  exact ((hX.add hA).continuousQuadraticVariation_congr (hX.add (hA.const_mul 1)) hF he).trans
    (hX.continuousQuadraticVariation_add_const_mul_finiteVariation hA hF hv 1)

theorem IsSemimartingale.continuousQuadraticVariation_sub_finiteVariation
    (hX : IsSemimartingale X F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths A P) :
    Indistinguishable ((hX.sub hA).continuousQuadraticVariation hF)
      (hX.continuousQuadraticVariation hF) P := by
  have he : Indistinguishable (X - A) (X + fun t ω ↦ (-1 : ℝ) * A t ω) P :=
    Filter.Eventually.of_forall (fun ω t ↦ by simp only [Pi.sub_apply, Pi.add_apply]; ring)
  exact ((hX.sub hA).continuousQuadraticVariation_congr (hX.add (hA.const_mul (-1))) hF he).trans
    (hX.continuousQuadraticVariation_add_const_mul_finiteVariation hA hF hv (-1))

end ProbabilityTheory
