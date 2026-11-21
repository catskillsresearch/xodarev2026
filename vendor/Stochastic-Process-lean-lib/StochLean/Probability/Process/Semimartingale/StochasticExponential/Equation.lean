/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Preservation
public import StochLean.Probability.Process.Semimartingale.StochasticExponential.ProductPureJump
public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Jump
public import StochLean.Probability.Process.Semimartingale.Ito.ExponentialProduct
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.PureJumpFiniteVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousDrift

/-! # The general stochastic-exponential integral equation

The actual product-defined process satisfies the equation, including paths
with zero or negative jump multipliers. The proof never divides by that
process. Initial values remain arbitrary until the unit-initial corollary.
Uniqueness is a separate theorem, not an assumption in this construction.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticExponential_sub_initial_eq_integral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    let hE := hX.isSemimartingale_stochasticExponential hF
    Indistinguishable
      (fun t ω ↦ hX.stochasticExponential hF t ω - Real.exp (X 0 ω))
      (hX.stochasticIntegral hF
        (hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths)
        hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess) P := by
  dsimp only
  let Q := hX.continuousQuadraticVariation hF
  let B := fun t ω ↦ (1 / 2 : ℝ) * Q t ω
  let K := X - B
  let S := stochasticExponentialJumpProduct X
  let E := hX.stochasticExponential hF
  let hQ := hX.isSemimartingale_continuousQuadraticVariation hF
  let hB := hQ.const_mul (1 / 2)
  have hK : IsSemimartingale K F P := hX.sub hB
  let hS := hX.isSemimartingale_stochasticExponentialJumpProduct hF
  let hE := hX.isSemimartingale_stochasticExponential hF
  let haL := hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths
  let hrL := hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let A := fun t ω ↦ Real.exp (K t ω)
  let haA : Adapted F A := fun t ↦ Real.continuous_exp.measurable.comp (hK.adapted t)
  let hrA := hK.hasCadlagPaths.continuous_comp Real.continuous_exp
  let haLA := haA.leftLimitProcess_of_usual hF hrA
  let hrLA := hrA.hasCagladPaths_leftLimitProcess
  have hvB : HasFiniteVariationPaths B P := by
    apply Filter.Eventually.of_forall
    intro ω
    have hm : Monotone (B · ω) := fun _ _ hst ↦ mul_le_mul_of_nonneg_left
      (hX.monotone_continuousQuadraticVariation hF ω hst) (by norm_num)
    exact (hm.monotoneOn univ).locallyBoundedVariationOn
  have hcB (ω : Ω) : IsContinuousPath (B · ω) :=
    (hX.continuous_continuousQuadraticVariation hF ω).const_mul (1 / 2)
  have hvS := hX.hasFiniteVariationPaths_stochasticExponentialJumpProduct hF
  have hjS : ∀ᵐ ω ∂P, ∀ t, S t ω - S 0 ω = ∑' s : Ioc 0 t, jumpProcess S s ω := by
    simpa only [S, stochasticExponentialJumpProduct_zero] using
      hX.stochasticExponentialJumpProduct_sub_one_eq_tsum_jumps hF
  have hJS := hS.stochasticIntegral_of_pureJump_finiteVariation hF hvS hjS haLA hrLA
  have hJQ := IsSemimartingale.stochasticIntegral_congr_integrator
    (hK.isSemimartingale_continuousQuadraticVariation hF) hQ hF haL hrL
    (hX.continuousQuadraticVariation_sub_finiteVariation hB hF hvB)
  have hi := hK.ito_exponential_mul_finiteVariation hS hF hvS
  filter_upwards [hi, hJS, hJQ, hX.hasCadlagPaths, hS.hasCadlagPaths,
    hX.jump_stochasticExponential_of_pos hF,
    hX.stochasticIntegral_sub_integrator hB hF haL hrL,
    hQ.stochasticIntegral_const_mul_integrator hF haL hrL (1 / 2)]
      with ω hiω hJSω hJQω hx hs hjE hsub hscale t
  have hk := hx.sub (hcB ω).isCadlagPath
  have hla (s : ℝ≥0) (hp : 0 < s) :
      leftLimitProcess A s ω = Real.exp (leftLimitProcess K s ω) :=
    hk.leftLimitProcess_continuous_comp_of_pos Real.continuous_exp hp
  have hle (s : ℝ≥0) (hp : 0 < s) :
      leftLimitProcess E s ω = Real.exp (leftLimitProcess K s ω) *
        leftLimitProcess S s ω := by
    change leftLimitProcess (A * S) s ω = _
    rw [(hk.continuous_comp Real.continuous_exp).leftLimitProcess_mul hs s, hla s hp]
  have hjk (s : ℝ≥0) (hp : 0 < s) : jumpProcess K s ω = jumpProcess X s ω := by
    rw [hx.jumpProcess_sub (hcB ω).isCadlagPath s,
      (hcB ω).jumpProcess_eq_zero (ne_of_gt hp), sub_zero]
  have hrem (s : Ioc 0 t) :
      E s ω - Real.exp (leftLimitProcess K s ω) * leftLimitProcess S s ω -
        Real.exp (leftLimitProcess K s ω) * leftLimitProcess S s ω * jumpProcess K s ω -
        Real.exp (leftLimitProcess K s ω) * jumpProcess S s ω =
      -(leftLimitProcess A s ω * jumpProcess S s ω) := by
    rw [← hle s s.2.1, hjk s s.2.1, hla s s.2.1]
    have he := hjE s s.2.1
    change E s ω - leftLimitProcess E s ω = _ at he
    linarith only [he]
  have hform := hiω t
  change E t ω - E 0 ω = hK.stochasticIntegral hF haL hrL t ω +
    hS.stochasticIntegral hF haLA hrLA t ω +
    (1 / 2 : ℝ) * (hK.isSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
      hF haL hrL t ω +
    ∑' s : Ioc 0 t, (E s ω - Real.exp (leftLimitProcess K s ω) *
      leftLimitProcess S s ω - Real.exp (leftLimitProcess K s ω) *
      leftLimitProcess S s ω * jumpProcess K s ω -
      Real.exp (leftLimitProcess K s ω) * jumpProcess S s ω) at hform
  simp only [hrem, tsum_neg] at hform
  rw [hsub t, hJQω t, hJSω t] at hform
  simp only [Pi.sub_apply, hscale t, Pi.smul_apply, smul_eq_mul,
    leftLimitProcess_zero, Pi.zero_apply, zero_mul, zero_add] at hform
  change E t ω - Real.exp (X 0 ω) = _
  have hinit : E 0 ω = Real.exp (X 0 ω) := hX.stochasticExponential_zero hF ω
  rw [hinit] at hform
  exact hform.trans (by ring)

theorem IsSemimartingale.stochasticExponential_eq_one_add_integral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (h0 : X 0 =ᵐ[P] 0) :
    let hE := hX.isSemimartingale_stochasticExponential hF
    Indistinguishable (hX.stochasticExponential hF)
      (fun t ω ↦ 1 + hX.stochasticIntegral hF
        (hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths)
        hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess t ω) P := by
  dsimp only
  filter_upwards [hX.stochasticExponential_sub_initial_eq_integral hF, h0]
    with ω hi hz t
  have h := hi t
  simp only [hz, Pi.zero_apply, Real.exp_zero] at h
  linarith only [h]

end ProbabilityTheory
