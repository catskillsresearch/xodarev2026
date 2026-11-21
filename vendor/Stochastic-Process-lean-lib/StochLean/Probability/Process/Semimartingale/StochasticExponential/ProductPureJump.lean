/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.ProductVariation
public import StochLean.Analysis.PathVariation.CumulativeProductPureJump
public import StochLean.Analysis.PathVariation.VariationJumpSeries

/-! # The stochastic-exponential jump product is genuinely pure jump

The actual positive-time jump series is absolutely summable and recovers
the product minus one. These are pathwise results, not an assumption of
adaptedness or of the stochastic integral equation.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticExponentialJumpProduct_sub_one_eq_tsum_jumps
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, stochasticExponentialJumpProduct X t ω - 1 =
      ∑' s : Ioc 0 t, jumpProcess (stochasticExponentialJumpProduct X) s ω := by
  filter_upwards [hX.summable_sq_jumps hF] with ω hs t
  have he (s : Ioc 0 t) :
      leftLimitProcess (stochasticExponentialJumpProduct X) s ω =
        Function.leftLim (fun v ↦ stochasticExponentialJumpProduct X v ω) s := by
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  simpa only [jumpProcess, Pi.sub_apply, he, stochasticExponentialJumpProduct] using
    tprod_Ioc_sub_one_eq_tsum_jumps
      (f := fun s ↦ exponentialJumpFactor (jumpProcess X s ω))
      (fun T ↦ summable_abs_exponentialJumpFactor_sub_one (hs T)) t

theorem IsSemimartingale.summable_abs_jumps_stochasticExponentialJumpProduct
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ |jumpProcess (stochasticExponentialJumpProduct X) s ω|) := by
  filter_upwards [hX.hasFiniteVariationPaths_stochasticExponentialJumpProduct hF,
    hX.hasCadlagPaths_stochasticExponentialJumpProduct hF] with ω hv hr t
  have he (s : Ioc 0 t) :
      leftLimitProcess (stochasticExponentialJumpProduct X) s ω =
        Function.leftLim (fun v ↦ stochasticExponentialJumpProduct X v ω) s := by
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  simpa only [jumpProcess, Pi.sub_apply, he] using
    summable_abs_jumps_of_locallyBoundedVariation hv hr.1 t

end ProbabilityTheory
