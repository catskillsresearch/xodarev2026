/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.RiemannSourceConvergence
public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.RiemannUniformContinuity
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.CagladInitialIncrement
public import StochLean.Probability.Process.Partition.LeftSamplingAlgebra
public import StochLean.Probability.Process.UCP.UniformApproximation

/-! # Random Riemann approximation for caglad integrands

Uniform source-simple approximation and partition-uniform continuity pass the
fixed-step displacement theorem to general adapted caglad integrands. Both the
explicit initial correction and Protter's exact source-left-limit form are
provided, without assuming that either initial random variable vanishes.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_leftRiemannSum_of_caglad
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F Y) (hr : HasCagladPaths Y P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess Y X) atTop
      (fun t ω ↦ hX.stochasticIntegral hF ha hr t ω - Y 0 ω * X 0 ω) := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  choose R hR using hS
  have hS (k : ℕ) : IsSimplePredictable (S k) F := ⟨R k, hR k⟩
  let C : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω ↦
    (R k).integralProcess X t ω - (R k).initial ω * X 0 ω
  have hC : TendstoUCP P C atTop
      (fun t ω ↦ hX.stochasticIntegral hF ha hr t ω - Y 0 ω * X 0 ω) := by
    have hu := (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).initialIncrement
    have heq (k : ℕ) : (hS k).elementaryIntegralProcess X = (R k).integralProcess X :=
      (hS k).elementaryIntegralProcess_eq (R k) (hR k) X
    simp only [heq, SimplePredictableRep.integralProcess_zero] at hu
    apply hu.congr_right
    filter_upwards [hX.stochasticIntegral_zero_ae hF ha hr] with ω hω t
    rw [hω]
  apply tendstoUCP_of_uniform_approximation
    (A := fun k n ↦ (π n).leftRiemannSumProcess (R k).toProcess X) (C := C) _ hC
  · intro n
    have hzero : TendstoUCP P (fun k ↦ S k - Y) atTop 0 := by
      simpa only [sub_self] using huS.sub (tendstoUCP_const atTop Y)
    have hu := hX.tendstoUCP_leftRiemannSum_zero_of_leftContinuous hF (fun k ↦ π (n k))
      (fun k ↦ (hS k).adapted.sub ha)
      (fun k ↦ (((hS k).hasCagladPaths P).sub hr).hasLeftContinuousPaths) hzero
    simpa only [StoppingTimePartition.leftRiemannSumProcess_sub_integrand, hR] using hu
  · intro k
    exact (R k).tendstoUCP_leftRiemannSum_toProcess hπ hX.adapted hF hX.hasCadlagPaths

theorem IsSemimartingale.tendstoUCP_leftRiemannSum_leftLimit_of_caglad
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F Y) (hr : HasCagladPaths Y P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess Y X) atTop
      (hX.stochasticIntegral hF
        (ha.leftLimitProcess_of_leftContinuous_usual hF hr.hasLeftContinuousPaths)
        hr.hasCagladPaths_leftLimitProcess) :=
  (hX.tendstoUCP_leftRiemannSum_of_caglad hF ha hr hπ).congr_right
    (hX.stochasticIntegral_leftLimit_of_caglad hF ha hr).symm

end ProbabilityTheory
