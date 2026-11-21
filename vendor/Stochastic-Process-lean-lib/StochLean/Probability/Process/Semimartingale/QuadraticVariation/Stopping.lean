/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Riemann
public import StochLean.Probability.Process.Semimartingale.Stopping
public import StochLean.Probability.Process.Partition.SquareSumsStopping
public import StochLean.Probability.Process.Partition.Klenke
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # Stopping the canonical raw quadratic variation

Exact stopping of the partition square sums and uniqueness of their UCP
limits prove the identity, including zero and infinite stopping times.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticVariation_stoppedProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable ((hX.stoppedProcess hF hτ).quadraticVariation hF)
      (MeasureTheory.stoppedProcess (hX.quadraticVariation hF) τ) P := by
  let π : ℕ → StoppingTimePartition F := fun n ↦ StoppingTimePartition.deterministic F
    ((StochLean.LocallyFinitePartition.dyadic n).restrict n)
  have hπ : StoppingTimePartition.IsTendingToIdentity π P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      StochLean.LocallyFinitePartition.dyadic_admissible tendsto_natCast_atTop_atTop
  have hstop := (hX.tendstoUCP_quadraticVariationSumProcess hF hπ).stoppedProcess τ
  have hu : TendstoUCP P
      (fun n ↦ (π n).quadraticVariationSumProcess (MeasureTheory.stoppedProcess X τ)) atTop
      (MeasureTheory.stoppedProcess (hX.quadraticVariation hF) τ) := by
    simpa only [StoppingTimePartition.quadraticVariationSumProcess_stoppedProcess] using hstop
  have huX := (hX.stoppedProcess hF hτ).tendstoUCP_quadraticVariationSumProcess hF hπ
  exact huX.indistinguishable_unique hu
    ((hX.stoppedProcess hF hτ).hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
    ((hX.hasCadlagPaths_quadraticVariation hF).stoppedProcess τ).hasRightContinuousPaths

end ProbabilityTheory
