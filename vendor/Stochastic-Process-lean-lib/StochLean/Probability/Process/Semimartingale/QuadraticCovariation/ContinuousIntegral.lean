/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Integral
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegralDecomposition
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra

/-! # Continuous covariation of stochastic integrals

The raw integral identity, its actual jumps and initial value, and the
proved continuous/atomic split identify the existing continuous owners.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H K : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_stochasticIntegral_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF ha hr).continuousQuadraticCovariation hY hF)
      ((hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral
        hF ha hr) P := by
  let hJ := hX.isSemimartingale_stochasticIntegral hF ha hr
  filter_upwards [hX.quadraticCovariation_stochasticIntegral_left hY hF ha hr,
    hJ.quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.stochasticIntegral_quadraticCovariation_continuous_jump_decomposition hY hF ha hr,
    hX.stochasticIntegral_zero_ae hF ha hr, hX.jumpProcess_stochasticIntegral hF ha hr]
      with ω hraw hd hi h0 hj t
  have hd' := (hd t).2
  rw [hraw t, hi t, h0] at hd'
  have he : (∑' s : Ioc 0 t, jumpProcess (hX.stochasticIntegral hF ha hr) s ω *
      jumpProcess Y s ω) = ∑' s : Ioc 0 t, H s ω * (jumpProcess X s ω * jumpProcess Y s ω) := by
    apply tsum_congr
    intro s
    rw [hj s, mul_assoc]
  rw [he] at hd'
  linarith only [hd']

theorem IsSemimartingale.continuousQuadraticCovariation_stochasticIntegral_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      (hX.continuousQuadraticCovariation (hY.isSemimartingale_stochasticIntegral hF ha hr) hF)
      ((hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral
        hF ha hr) P := by
  have hi := IsSemimartingale.stochasticIntegral_congr_integrator
    (hY.isSemimartingale_continuousQuadraticCovariation hX hF)
    (hX.isSemimartingale_continuousQuadraticCovariation hY hF) hF ha hr
    (hY.continuousQuadraticCovariation_comm hX hF)
  exact (hX.continuousQuadraticCovariation_comm
    (hY.isSemimartingale_stochasticIntegral hF ha hr) hF).trans
      ((hY.continuousQuadraticCovariation_stochasticIntegral_left hX hF ha hr).trans hi)

theorem IsSemimartingale.continuousQuadraticCovariation_stochasticIntegral_both
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF haH hrH).continuousQuadraticCovariation
        (hY.isSemimartingale_stochasticIntegral hF haK hrK) hF)
      ((hX.isSemimartingale_continuousQuadraticCovariation hY hF).stochasticIntegral hF
        (fun t ↦ (haH t).mul (haK t)) (hrH.mul hrK)) P := by
  let hJY := hY.isSemimartingale_stochasticIntegral hF haK hrK
  let hB := hX.isSemimartingale_continuousQuadraticCovariation hY hF
  have hi := IsSemimartingale.stochasticIntegral_congr_integrator
    (hX.isSemimartingale_continuousQuadraticCovariation hJY hF)
    (hB.isSemimartingale_stochasticIntegral hF haK hrK) hF haH hrH
    (hX.continuousQuadraticCovariation_stochasticIntegral_right hY hF haK hrK)
  exact (hX.continuousQuadraticCovariation_stochasticIntegral_left hJY hF haH hrH).trans
    (hi.trans (hB.stochasticIntegral_stochasticIntegral hF haH hrH haK hrK))

end ProbabilityTheory
