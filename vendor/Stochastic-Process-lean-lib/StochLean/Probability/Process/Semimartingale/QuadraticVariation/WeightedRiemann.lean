/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.WeightedRiemann
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Algebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance

/-! # Weighted square sums against the sole raw square bracket

The existing mixed-sum owner is specialized on the diagonal. Bracket
invariance identifies its integral with the existing raw QV integral.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_weightedQuadraticVariationSum
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCadlagPaths H P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).weightedQuadraticCovariationSumProcess H X X) atTop
      ((hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF
        (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess) :=
  (hX.tendstoUCP_weightedQuadraticCovariationSum hX hF ha hr hπ).congr_right
    ((hX.isSemimartingale_quadraticCovariation hX hF).stochasticIntegral_congr_integrator
      (hX.isSemimartingale_quadraticVariation hF) hF
      (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess
      (hX.quadraticCovariation_self hF))

end ProbabilityTheory
