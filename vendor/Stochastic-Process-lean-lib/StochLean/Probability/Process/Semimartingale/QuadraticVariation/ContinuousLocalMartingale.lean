/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousPaths
public import StochLean.Probability.Process.LocalMartingale.Stability

/-! # The local-martingale assertion of Protter II.27

For a continuous local martingale, the square minus its existing raw quadratic
variation is a continuous local martingale. No new bracket or moment assumption
is introduced. The nondegeneracy and constancy consequences are separate work.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.isContinuousLocalMartingale_sq_sub_quadraticVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsContinuousLocalMartingale
      ((fun t ω ↦ (X t ω) ^ 2) - (hX.isSemimartingale hF).quadraticVariation hF) F P := by
  let hSM := hX.isSemimartingale hF
  let ha := hSM.adapted.leftLimitProcess_of_usual hF hSM.hasCadlagPaths
  let hr := hSM.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hJ := hX.isContinuousLocalMartingale_stochasticIntegral hF ha hr
  have heq : (fun t ω ↦ (X t ω) ^ 2) - hSM.quadraticVariation hF =
      (2 : ℝ) • hSM.stochasticIntegral hF ha hr := by
    funext t ω
    simp only [IsSemimartingale.quadraticVariation, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  refine ⟨hJ.1.const_smul 2, ?_⟩
  filter_upwards [hJ.2] with ω hj
  exact continuous_const.mul hj

theorem IsContinuousLocalMartingale.hasContinuousPaths_quadraticVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    HasContinuousPaths ((hX.isSemimartingale hF).quadraticVariation hF) P := by
  have hN := (hX.isContinuousLocalMartingale_sq_sub_quadraticVariation hF).2
  filter_upwards [hX.2, hN] with ω hx hn
  have hcont := (hx.pow 2).sub hn
  change Continuous (fun t ↦ (hX.isSemimartingale hF).quadraticVariation hF t ω)
  convert hcont using 1
  funext t
  simp only [Pi.sub_apply, Pi.pow_apply]
  ring

end ProbabilityTheory
