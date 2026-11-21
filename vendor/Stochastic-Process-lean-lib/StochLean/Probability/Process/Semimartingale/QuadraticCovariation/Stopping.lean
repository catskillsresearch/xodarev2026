/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Riemann
public import StochLean.Probability.Process.Semimartingale.Stopping
public import StochLean.Probability.Process.Partition.CrossSumsStopping

/-! # Stopping both arguments of raw quadratic covariation

The finite sums commute with simultaneous stopping, hence so does their
unique UCP limit. Zero and infinite stopping times are included.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_stoppedProcess_both
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      ((hX.stoppedProcess hF hτ).quadraticCovariation (hY.stoppedProcess hF hτ) hF)
      (MeasureTheory.stoppedProcess (hX.quadraticCovariation hY hF) τ) P := by
  apply (hX.stoppedProcess hF hτ).quadraticCovariation_indistinguishable_of_limits
    (hY.stoppedProcess hF hτ) hF
  · intro π hπ
    simpa only [StoppingTimePartition.quadraticCovariationSumProcess_stoppedProcess] using
      (hX.tendstoUCP_quadraticCovariationSumProcess hY hF hπ).stoppedProcess τ
  · exact ((hX.hasCadlagPaths_quadraticCovariation hY hF).stoppedProcess τ).hasRightContinuousPaths

end ProbabilityTheory
