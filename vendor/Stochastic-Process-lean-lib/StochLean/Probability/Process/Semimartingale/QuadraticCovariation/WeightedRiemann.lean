/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegralAlgebra
public import StochLean.Probability.Process.Partition.WeightedCrossSums
public import StochLean.Probability.Process.Path.LeftLimitMultiplication

/-! # Protter II.30: weighted random-partition mixed sums

For an adapted cadlag weight H, actual weighted increment sums converge in
UCP to the constructed integral of H₋ against the unique raw mixed bracket.
The source H₀₋ is zero. No boundedness, moment, continuity or deterministic
partition assumption is added. The proof uses II.21 and associativity, not
an invalid uniform approximation of a discontinuous sampled integrand.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_weightedQuadraticCovariationSum
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCadlagPaths H P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).weightedQuadraticCovariationSumProcess H X Y) atTop
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF
        (ha.leftLimitProcess_of_usual hF hr) hr.hasCagladPaths_leftLimitProcess) := by
  let haHL := ha.leftLimitProcess_of_usual hF hr
  let hrHL := hr.hasCagladPaths_leftLimitProcess
  let haHX : Adapted F (H * X) := fun t ↦ (ha t).mul (hX.adapted t)
  let haHY : Adapted F (H * Y) := fun t ↦ (ha t).mul (hY.adapted t)
  let hrHX := hr.mul hX.hasCadlagPaths
  let hrHY := hr.mul hY.hasCadlagPaths
  have hu := ((hX.mul hY hF).tendstoUCP_leftRiemannSum_leftLimit_of_cadlag hF ha hr hπ).sub
    (hY.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag hF haHX hrHX hπ)
  have hu' := hu.sub (hX.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag hF haHY hrHY hπ)
  have hbridge := hX.stochasticIntegral_quadraticCovariation_eq hY hF haHL hrHL
  have hYeq := hY.stochasticIntegral_congr_integrand hF
    (haHX.leftLimitProcess_of_usual hF hrHX) hrHX.hasCagladPaths_leftLimitProcess
    (fun t ↦ (haHL t).mul
      (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths t))
    (hrHL.mul hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess)
    (hr.leftLimitProcess_mul hX.hasCadlagPaths)
  have hXeq := hX.stochasticIntegral_congr_integrand hF
    (haHY.leftLimitProcess_of_usual hF hrHY) hrHY.hasCagladPaths_leftLimitProcess
    (fun t ↦ (haHL t).mul
      (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths t))
    (hrHL.mul hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess)
    (hr.leftLimitProcess_mul hY.hasCadlagPaths)
  have htarget : Indistinguishable
      ((hX.mul hY hF).stochasticIntegral hF haHL hrHL -
        hY.stochasticIntegral hF (haHX.leftLimitProcess_of_usual hF hrHX)
          hrHX.hasCagladPaths_leftLimitProcess -
        hX.stochasticIntegral hF (haHY.leftLimitProcess_of_usual hF hrHY)
          hrHY.hasCagladPaths_leftLimitProcess)
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF haHL hrHL) P := by
    filter_upwards [hbridge, hYeq, hXeq] with ω hb hy hx t
    simp only [Pi.sub_apply, hb t, hy t, hx t]
  simpa only [StoppingTimePartition.weightedQuadraticCovariationSumProcess_eq_riemann]
    using hu'.congr_right htarget

end ProbabilityTheory
