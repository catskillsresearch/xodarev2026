/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Basic
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra

/-! # Version invariance of the actual stochastic exponential -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticExponential_congr
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (he : Indistinguishable X Y P) :
    Indistinguishable (hX.stochasticExponential hF) (hY.stochasticExponential hF) P := by
  filter_upwards [he, he.jumpProcess, hX.continuousQuadraticVariation_congr hY hF he]
    with ω heω hj hq t
  simp only [stochasticExponential, stochasticExponentialJumpProduct, heω t, hq t, hj]

end ProbabilityTheory
