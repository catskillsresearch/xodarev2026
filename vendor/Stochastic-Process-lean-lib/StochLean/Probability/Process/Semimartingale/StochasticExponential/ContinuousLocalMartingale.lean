/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.ContinuousEquation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalL2
public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale
public import StochLean.Probability.Process.LocalMartingale.Congr

/-! # Stochastic exponentials of continuous local martingales

Masked local square integrability supplies integral preservation. The
arbitrary F0-measurable initial value is retained, without assuming its
exponential integrable or asserting that the result is a true martingale.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsContinuousLocalMartingale.isContinuousLocalMartingale_stochasticExponential
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsContinuousLocalMartingale ((hM.isSemimartingale hF).stochasticExponential hF) F P := by
  let hX := hM.isSemimartingale hF
  let hE := hX.isSemimartingale_stochasticExponential_of_continuous hF hM.2
  let haL := hE.adapted.leftLimitProcess_of_usual hF hE.hasCadlagPaths
  let hrL := hE.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hJ := hX.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable hF
    (hM.locally_squareIntegrableMartingale hF) haL hrL
  have hI := isContinuousLocalMartingale_const_initial (P := P)
    (Real.continuous_exp.measurable.comp (hX.adapted 0))
  have he : Indistinguishable
      ((fun (_ : ℝ≥0) ω ↦ Real.exp (X 0 ω)) + hX.stochasticIntegral hF haL hrL)
      (hX.stochasticExponential hF) P := by
    filter_upwards [hX.stochasticExponential_sub_initial_eq_integral_of_continuous hF hM.2]
      with ω heω t
    have h := heω t
    change Real.exp (X 0 ω) + hX.stochasticIntegral hF haL hrL t ω = _
    linarith only [h]
  exact ⟨(hI.1.add hJ hF).congr hF hE.adapted he,
    hX.hasContinuousPaths_stochasticExponential_of_continuous hF hM.2⟩

end ProbabilityTheory
