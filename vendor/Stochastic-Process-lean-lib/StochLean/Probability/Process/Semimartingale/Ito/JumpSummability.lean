/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CadlagC2JumpSeries
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPart

/-! # Actual absolute jump-remainder series for C2 semimartingale calculus

The conclusion holds on a common event for all finite horizons. It uses
the square-summable jumps of the original raw bracket, not FV paths of X.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.summable_abs_contDiff_jump_remainders
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦
      |f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω|) := by
  filter_upwards [hX.hasCadlagPaths, hX.summable_sq_jumps hF] with ω hx hs t
  have he (s : Ioc 0 t) : leftLimitProcess X s ω = Function.leftLim (X · ω) s := by
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hsq : Summable (fun s : Ioc 0 t ↦ (X s ω - Function.leftLim (X · ω) s) ^ 2) := by
    simpa only [jumpProcess, Pi.sub_apply, he] using hs t
  simpa only [jumpProcess, Pi.sub_apply, he] using
    summable_abs_contDiff_jump_remainders_of_summable_sq hx hsq hf

theorem IsSemimartingale.summable_abs_contDiff_second_order_jump_remainders
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦
      |f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
        deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2|) := by
  filter_upwards [hX.hasCadlagPaths, hX.summable_sq_jumps hF] with ω hx hs t
  have he (s : Ioc 0 t) : leftLimitProcess X s ω = Function.leftLim (X · ω) s := by
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hsq : Summable (fun s : Ioc 0 t ↦ (X s ω - Function.leftLim (X · ω) s) ^ 2) := by
    simpa only [jumpProcess, Pi.sub_apply, he] using hs t
  simpa only [jumpProcess, Pi.sub_apply, he] using
    StochLean.summable_abs_contDiff_second_order_jump_remainders hx hsq hf

end ProbabilityTheory
