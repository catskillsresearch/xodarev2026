/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Cadlag
public import StochLean.Analysis.PathVariation.CumulativeProductVariation

/-! # Finite variation of the actual stochastic-exponential jump product

This is a pathwise conclusion on one full-measure event for every horizon.
No expected-variation bound, nonvanishing hypothesis, or adaptedness of
an uncountably indexed product is silently assumed.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.hasFiniteVariationPaths_stochasticExponentialJumpProduct
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (stochasticExponentialJumpProduct X) P := by
  filter_upwards [hX.summable_sq_jumps hF] with ω hs
  exact locallyBoundedVariationOn_tprod_Ioc
    (f := fun s ↦ exponentialJumpFactor (jumpProcess X s ω))
    (fun T ↦ summable_abs_exponentialJumpFactor_sub_one (hs T))

end ProbabilityTheory
