/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialIncrement
public import StochLean.Probability.Process.Measurability.CagladLeftLimit

/-! # Initial normalization for general caglad integrands -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_leftLimit_of_caglad
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      (hX.stochasticIntegral hF
        (ha.leftLimitProcess_of_leftContinuous_usual hF hr.hasLeftContinuousPaths)
        hr.hasCagladPaths_leftLimitProcess)
      (fun t ω ↦ hX.stochasticIntegral hF ha hr t ω - H 0 ω * X 0 ω) P := by
  let K := cutoffIntegrand H (fun _ ↦ (0 : WithTop ℝ≥0))
  have haK : Adapted F K := adapted_cutoffIntegrand ha (isStoppingTime_const F 0)
  have hrK : HasCagladPaths K P := hr.cutoffIntegrand _
  have hI := hX.stochasticIntegral_congr_integrand hF
    (ha.leftLimitProcess_of_leftContinuous_usual hF hr.hasLeftContinuousPaths)
    hr.hasCagladPaths_leftLimitProcess (fun t ↦ (ha t).sub (haK t)) (hr.sub hrK)
    hr.hasLeftContinuousPaths.leftLimitProcess_eq_sub_cutoff_zero
  filter_upwards [hI, hX.stochasticIntegral_sub hF ha hr haK hrK,
    hX.stochasticIntegral_cutoff_zero hF ha hr] with ω he hsub hz t
  exact (he t).trans ((hsub t).trans (congrArg (fun a ↦
    hX.stochasticIntegral hF ha hr t ω - a) (hz t)))

end ProbabilityTheory
