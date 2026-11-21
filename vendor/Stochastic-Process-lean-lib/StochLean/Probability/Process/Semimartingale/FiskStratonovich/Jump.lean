/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.FiskStratonovich.Basic

/-! # Jumps of the source Fisk--Stratonovich integral

The continuous correction contributes no jump, including at zero. In
particular simultaneous jumps do not acquire a spurious half-product term.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.jumpProcess_fiskStratonovichIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (jumpProcess (hX.fiskStratonovichIntegral hY hF))
      (fun t ω ↦ leftLimitProcess Y t ω * jumpProcess X t ω) P := by
  let ha := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hr := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let C : ℝ≥0 → Ω → ℝ := (1 / 2 : ℝ) • hY.continuousQuadraticCovariation hX hF
  have hc (ω : Ω) : IsContinuousPath (C · ω) :=
    (hY.continuous_continuousQuadraticCovariation hX hF ω).const_mul (1 / 2)
  filter_upwards [hX.jumpProcess_stochasticIntegral hF ha hr] with ω hj t
  have hz : jumpProcess C t ω = 0 := by
    by_cases ht : t = 0
    · subst t
      simp only [jumpProcess_zero, C, Pi.smul_apply, smul_eq_mul,
        IsSemimartingale.continuousQuadraticCovariation_zero, mul_zero]
    · exact (hc ω).jumpProcess_eq_zero ht
  change jumpProcess (hX.stochasticIntegral hF ha hr + C) t ω = _
  rw [(hX.isCadlagPath_stochasticIntegral hF ha hr ω).jumpProcess_add
    (hc ω).isCadlagPath t, hz, add_zero]
  exact hj t

end ProbabilityTheory
