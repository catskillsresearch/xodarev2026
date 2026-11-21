/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.RiemannConvergence
public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.RiemannUniformContinuity
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue
public import StochLean.Probability.Process.Partition.LeftSamplingAlgebra
public import StochLean.Probability.Process.Path.LeftRightReconstruction
public import StochLean.Probability.Process.UCP.RightLimit
public import StochLean.Probability.Process.UCP.UniformApproximation

/-! # Random Riemann approximation for cadlag integrands

Left sampling of a discontinuous path need not converge uniformly to its left
limit. We instead approximate that left limit by source simple processes, take
their right limits, and use partition-uniform continuity of the Riemann sums.
The limit is the source integral of `Y₋`, with its prescribed zero initial value.
There is no restriction on the integrator's initial random variable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F Y) (hr : HasCadlagPaths Y P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess Y X) atTop
      (hX.stochasticIntegral hF (ha.leftLimitProcess_of_usual hF hr)
        hr.hasCagladPaths_leftLimitProcess) := by
  let haL := ha.leftLimitProcess_of_usual hF hr
  let hrL := hr.hasCagladPaths_leftLimitProcess
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP haL hF hrL
  choose R hR using hS
  have hS (k : ℕ) : IsSimplePredictable (S k) F := ⟨R k, hR k⟩
  have huR : TendstoUCP P (fun k ↦ (R k).toProcess) atTop (leftLimitProcess Y) := by
    simpa only [hR] using huS
  have hrR (k : ℕ) : HasCagladPaths (R k).toProcess P :=
    ae_of_all _ (R k).isCagladPath
  have huRight : TendstoUCP P (fun k ↦ rightLimitProcess (R k).toProcess) atTop Y :=
    (huR.rightLimitProcess_of_caglad hrR hrL).congr_right
      hr.rightLimitProcess_leftLimitProcess
  let C : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω ↦
    (R k).integralProcess X t ω - (R k).initial ω * X 0 ω
  have hC : TendstoUCP P C atTop (hX.stochasticIntegral hF haL hrL) := by
    have hu := (hX.tendstoUCP_stochasticIntegral_of_simple hF haL hrL hS huS).initialIncrement
    have heq (k : ℕ) : (hS k).elementaryIntegralProcess X = (R k).integralProcess X :=
      (hS k).elementaryIntegralProcess_eq (R k) (hR k) X
    simp only [heq, SimplePredictableRep.integralProcess_zero] at hu
    apply hu.congr_right
    filter_upwards [hX.stochasticIntegral_zero_ae hF haL hrL] with ω hω t
    simp only [leftLimitProcess_zero, Pi.zero_apply, zero_mul] at hω
    simp only [hω, sub_zero]
  apply tendstoUCP_of_uniform_approximation
    (A := fun k n ↦ (π n).leftRiemannSumProcess (rightLimitProcess (R k).toProcess) X)
    (C := C) _ hC
  · intro n
    have hzero : TendstoUCP P (fun k ↦ rightLimitProcess (R k).toProcess - Y) atTop 0 := by
      simpa only [sub_self] using huRight.sub (tendstoUCP_const atTop Y)
    have hu := hX.tendstoUCP_leftRiemannSum_zero_of_rightContinuous hF (fun k ↦ π (n k))
      (fun k ↦ ((R k).adapted.rightLimitProcess_of_usual hF (hrR k)).sub ha)
      (fun k ↦ ((hrR k).hasCadlagPaths_rightLimitProcess.sub hr).hasRightContinuousPaths) hzero
    simpa only [StoppingTimePartition.leftRiemannSumProcess_sub_integrand] using hu
  · intro k
    exact (R k).tendstoUCP_leftRiemannSum_rightLimitProcess hπ hX.adapted hF hX.hasCadlagPaths

end ProbabilityTheory
