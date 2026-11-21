/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeJumpSeries
public import StochLean.Probability.Process.Semimartingale.Ito.JumpSummability

/-! # Finite variation of both actual Ito jump-correction processes -/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.hasFiniteVariationPaths_contDiff_jump_remainders
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    HasFiniteVariationPaths (fun t ω ↦ ∑' s : Ioc 0 t,
      (f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω)) P := by
  filter_upwards [hX.summable_abs_contDiff_jump_remainders hF hf] with ω hs
  exact locallyBoundedVariationOn_tsum_Ioc
    (g := fun s ↦ f (X s ω) - f (leftLimitProcess X s ω) -
      deriv f (leftLimitProcess X s ω) * jumpProcess X s ω) hs

theorem IsSemimartingale.hasFiniteVariationPaths_contDiff_second_order_jump_remainders
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    HasFiniteVariationPaths (fun t ω ↦ ∑' s : Ioc 0 t,
      (f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
        deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)) P := by
  filter_upwards [hX.summable_abs_contDiff_second_order_jump_remainders hF hf] with ω hs
  exact locallyBoundedVariationOn_tsum_Ioc
    (g := fun s ↦ f (X s ω) - f (leftLimitProcess X s ω) -
      deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
      deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2) hs

end ProbabilityTheory
