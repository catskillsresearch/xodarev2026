/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Basic
public import StochLean.Analysis.PathVariation.CumulativeProduct
public import StochLean.Probability.Process.Path.Multiplication

/-! # Cadlag paths of the actual stochastic-exponential product expression

Local square-summability controls all factor deviations. The one-sided
product limits hold on a common event for every finite time, including
after a vanishing or negative factor.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.hasCadlagPaths_stochasticExponentialJumpProduct
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasCadlagPaths (stochasticExponentialJumpProduct X) P := by
  filter_upwards [hX.summable_sq_jumps hF] with ω hs
  exact isCadlagPath_tprod_Ioc (f := fun s ↦ exponentialJumpFactor (jumpProcess X s ω))
    (fun T ↦ summable_abs_exponentialJumpFactor_sub_one (hs T))

theorem IsSemimartingale.hasCadlagPaths_stochasticExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasCadlagPaths (hX.stochasticExponential hF) P := by
  filter_upwards [hX.hasCadlagPaths, hX.hasCadlagPaths_stochasticExponentialJumpProduct hF]
    with ω hx hp
  have hq := (hX.continuous_continuousQuadraticVariation hF ω).const_mul (1 / 2)
  have hK := hx.sub (IsContinuousPath.isCadlagPath hq)
  exact (hK.continuous_comp Real.continuous_exp).mul hp

end ProbabilityTheory
