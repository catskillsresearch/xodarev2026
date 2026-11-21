/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Riemann
public import StochLean.Probability.Process.Partition.CrossSums
public import StochLean.Probability.Process.Partition.Klenke
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # Mixed increment sums converge to the polarized raw covariation

The characterization below uses genuine partition limits, not an assumed
bilinearity of the square bracket or continuity in the integrator.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_quadraticCovariationSumProcess
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).quadraticCovariationSumProcess X Y) atTop
      (hX.quadraticCovariation hY hF) := by
  have hu := (((hX.add hY).tendstoUCP_quadraticVariationSumProcess hF hπ).sub
    (hX.tendstoUCP_quadraticVariationSumProcess hF hπ)).sub
      (hY.tendstoUCP_quadraticVariationSumProcess hF hπ)
  simp only [StoppingTimePartition.quadraticCovariationSumProcess_polarization]
  exact hu.smul (1 / 2 : ℝ)

theorem IsSemimartingale.quadraticCovariation_indistinguishable_of_limits
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hZ : ∀ (π : ℕ → StoppingTimePartition F),
      StoppingTimePartition.IsTendingToIdentity π P →
      TendstoUCP P (fun n ↦ (π n).quadraticCovariationSumProcess X Y) atTop Z)
    (hrZ : HasRightContinuousPaths Z P) :
    Indistinguishable (hX.quadraticCovariation hY hF) Z P := by
  let π : ℕ → StoppingTimePartition F := fun n ↦ StoppingTimePartition.deterministic F
    ((StochLean.LocallyFinitePartition.dyadic n).restrict n)
  have hπ : StoppingTimePartition.IsTendingToIdentity π P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      StochLean.LocallyFinitePartition.dyadic_admissible tendsto_natCast_atTop_atTop
  exact (hX.tendstoUCP_quadraticCovariationSumProcess hY hF hπ).indistinguishable_unique
    (hZ π hπ) (hX.hasCadlagPaths_quadraticCovariation hY hF).hasRightContinuousPaths hrZ

end ProbabilityTheory
