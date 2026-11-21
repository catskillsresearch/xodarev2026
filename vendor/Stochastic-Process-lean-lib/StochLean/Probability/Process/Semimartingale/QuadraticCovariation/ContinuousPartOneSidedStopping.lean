/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartStopping
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OneSidedStopping
public import StochLean.Probability.Process.Path.JumpSumStopping

/-! # Stopping either argument of continuous covariation

The already proved raw identity and the exact closed-endpoint jump cutoff give
the continuous-part identity. No incorrect one-sided finite-cell identity is used.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_stoppedProcess_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable ((hX.stoppedProcess hF hτ).continuousQuadraticCovariation hY hF)
      (MeasureTheory.stoppedProcess (hX.continuousQuadraticCovariation hY hF) τ) P := by
  filter_upwards
    [(hX.stoppedProcess hF hτ).quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.quadraticCovariation_stoppedProcess_left hY hF hτ, hX.hasCadlagPaths]
    with ω hs hx hraw hcx t
  have h0 : MeasureTheory.stoppedProcess X τ 0 ω = X 0 ω :=
    stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from bot_le)
  have h := (hs t).2
  rw [hraw t, h0, hcx.tsum_jump_mul_stoppedProcess τ t] at h
  change hX.quadraticCovariation hY hF ((min (t : WithTop ℝ≥0) (τ ω)).untopA) ω = _ at h
  change (hX.stoppedProcess hF hτ).continuousQuadraticCovariation hY hF t ω =
    hX.continuousQuadraticCovariation hY hF ((min (t : WithTop ℝ≥0) (τ ω)).untopA) ω
  linarith [(hx ((min (t : WithTop ℝ≥0) (τ ω)).untopA)).2]

theorem IsSemimartingale.continuousQuadraticCovariation_stoppedProcess_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable (hX.continuousQuadraticCovariation (hY.stoppedProcess hF hτ) hF)
      (MeasureTheory.stoppedProcess (hX.continuousQuadraticCovariation hY hF) τ) P :=
  (hX.continuousQuadraticCovariation_comm (hY.stoppedProcess hF hτ) hF).trans
    ((hY.continuousQuadraticCovariation_stoppedProcess_left hX hF hτ).trans
      ((hY.continuousQuadraticCovariation_comm hX hF).stoppedProcess τ))

end ProbabilityTheory
