/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessCongr

/-! # Invariance of the constructed integral under indistinguishable integrators

A common simple approximation works for both integrators. Its integral processes
are indistinguishable, and UCP uniqueness identifies the two constructed limits.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_congr_integrator
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hXY : Indistinguishable X Y P) :
    Indistinguishable (hX.stochasticIntegral hF ha hr) (hY.stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  apply hX.stochasticIntegral_indistinguishable_of_limit hF ha hr hS huS
  · exact (hY.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).congr_left
      (fun n ↦ (hS n).elementaryIntegralProcess_congr_integrator hXY.symm)
  · exact (hY.hasCadlagPaths_stochasticIntegral hF ha hr).hasRightContinuousPaths

end ProbabilityTheory
