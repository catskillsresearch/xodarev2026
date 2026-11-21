/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.Basic
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialIncrement

/-! # Continuous coordinates in the actual stochastic area

The initial products in the two integrals cancel by commutativity. Thus the
continuous-coordinate formula needs no zero-starting or integrability premise.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.stochasticArea_eq_integrals_of_continuous
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P) :
    Indistinguishable (hX.stochasticArea hY hF)
      (hY.stochasticIntegral hF hX.adapted hcX.hasCagladPaths -
        hX.stochasticIntegral hF hY.adapted hcY.hasCagladPaths) P := by
  filter_upwards [hY.stochasticIntegral_leftLimit_of_continuous hF hX.adapted hcX,
    hX.stochasticIntegral_leftLimit_of_continuous hF hY.adapted hcY] with ω hy hx t
  dsimp only [stochasticArea, Pi.sub_apply]
  rw [hy t, hx t]
  ring

end ProbabilityTheory
