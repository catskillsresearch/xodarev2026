/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Jump
public import StochLean.Probability.Process.Path.ContinuousOfJump
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalL2
public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale

/-! # Continuity and continuous-local-martingale preservation

A continuous integrator has no positive-time jumps. The proved jump formula
therefore makes its integral continuous, even for a discontinuous caglad
integrand. The source initial value remains arbitrary.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.hasContinuousPaths_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hc : HasContinuousPaths X P) :
    HasContinuousPaths (hX.stochasticIntegral hF ha hr) P := by
  apply (hX.hasCadlagPaths_stochasticIntegral hF ha hr).hasContinuousPaths_of_jumpProcess_eq_zero
  filter_upwards [hX.jumpProcess_stochasticIntegral hF ha hr, hc] with ω hj hx t ht
  rw [hj t, hx.jumpProcess_eq_zero ht, mul_zero]

theorem IsContinuousLocalMartingale.isContinuousLocalMartingale_stochasticIntegral
    [SigmaFiniteFiltration P F] (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsContinuousLocalMartingale ((hX.isSemimartingale hF).stochasticIntegral hF ha hr) F P :=
  ⟨(hX.isSemimartingale hF).isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable
      hF (hX.locally_squareIntegrableMartingale hF) ha hr,
    (hX.isSemimartingale hF).hasContinuousPaths_stochasticIntegral hF ha hr hX.2⟩

end ProbabilityTheory
