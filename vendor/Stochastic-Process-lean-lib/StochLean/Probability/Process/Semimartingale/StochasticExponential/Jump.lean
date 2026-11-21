/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Cadlag
public import StochLean.Analysis.PathVariation.CumulativeProductJump
public import StochLean.Probability.Process.Path.LeftLimitMultiplication
public import StochLean.Probability.Process.Path.LeftLimitCompositionPositive

/-! # Actual jumps of the stochastic exponential

The positive-time multiplier identity does not divide by either product.
It therefore remains valid at and after an absorbing jump of size -1.
Time zero is excluded: the source left limit there is zero, while the
exponential has initial value exp(X(0)).
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticExponential_eq_left_mul_one_add_jump
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      hX.stochasticExponential hF t ω =
        leftLimitProcess (hX.stochasticExponential hF) t ω * (1 + jumpProcess X t ω) := by
  filter_upwards [hX.hasCadlagPaths, hX.summable_sq_jumps hF,
    hX.hasCadlagPaths_stochasticExponentialJumpProduct hF] with ω hx hs hp t ht
  let Q : ℝ≥0 → Ω → ℝ := fun s v ↦ (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF s v
  let K := X - Q
  have hq : IsContinuousPath (Q · ω) :=
    (hX.continuous_continuousQuadraticVariation hF ω).const_mul (1 / 2)
  have hk : IsCadlagPath (K · ω) := hx.sub hq.isCadlagPath
  have hke := hk.continuous_comp Real.continuous_exp
  have ha (T : ℝ≥0) :
      Summable (fun s : Ioc 0 T ↦ |exponentialJumpFactor (jumpProcess X s ω) - 1|) :=
    summable_abs_exponentialJumpFactor_sub_one (hs T)
  have hlp : leftLimitProcess (stochasticExponentialJumpProduct X) t ω =
      ∏' s : Ioo 0 t, exponentialJumpFactor (jumpProcess X s ω) := by
    rw [leftLimitProcess, if_neg (ne_of_gt ht)]
    exact leftLim_tprod_Ioc (f := fun s ↦ exponentialJumpFactor (jumpProcess X s ω)) ha ht
  have hpt : stochasticExponentialJumpProduct X t ω =
      exponentialJumpFactor (jumpProcess X t ω) *
        leftLimitProcess (stochasticExponentialJumpProduct X) t ω := by
    rw [hlp]
    exact tprod_Ioc_eq_endpoint_mul_tprod_Ioo
      (f := fun s ↦ exponentialJumpFactor (jumpProcess X s ω)) (ha t) ht
  have hle : leftLimitProcess (hX.stochasticExponential hF) t ω =
      Real.exp (leftLimitProcess K t ω) *
        leftLimitProcess (stochasticExponentialJumpProduct X) t ω := by
    change leftLimitProcess ((fun s v ↦ Real.exp (K s v)) *
      stochasticExponentialJumpProduct X) t ω = _
    rw [hke.leftLimitProcess_mul hp t,
      hk.leftLimitProcess_continuous_comp_of_pos Real.continuous_exp ht]
  have hdiff : K t ω - jumpProcess X t ω = leftLimitProcess K t ω := by
    rw [hx.leftLimitProcess_sub hq.isCadlagPath t, hq.leftLimitProcess_eq (ne_of_gt ht)]
    simp only [K, Pi.sub_apply, jumpProcess]
    ring
  change Real.exp (K t ω) * stochasticExponentialJumpProduct X t ω = _
  rw [hpt, hle, exponentialJumpFactor]
  calc
    _ = Real.exp (K t ω + -jumpProcess X t ω) *
        leftLimitProcess (stochasticExponentialJumpProduct X) t ω *
          (1 + jumpProcess X t ω) := by rw [Real.exp_add]; ring
    _ = _ := by rw [← sub_eq_add_neg, hdiff]

theorem IsSemimartingale.jump_stochasticExponential_of_pos
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      jumpProcess (hX.stochasticExponential hF) t ω =
        leftLimitProcess (hX.stochasticExponential hF) t ω * jumpProcess X t ω := by
  filter_upwards [hX.stochasticExponential_eq_left_mul_one_add_jump hF] with ω hω t ht
  change hX.stochasticExponential hF t ω -
    leftLimitProcess (hX.stochasticExponential hF) t ω = _
  rw [hω t ht]
  ring

end ProbabilityTheory
