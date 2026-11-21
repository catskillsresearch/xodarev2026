/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.LeftSamplingRegularity
public import StochLean.Probability.Process.UCP.LeftSampling
public import StochLean.Probability.Process.UCP.InitialIncrement
public import StochLean.Probability.Process.Semimartingale.UCP

/-! # Partition-uniform UCP continuity of increment-only Riemann sums

The partitions may vary arbitrarily with the input index. Source UCP continuity
and the compact-deviation contraction give uniformity without a mesh condition.
The initial product is removed by stopping the same source integral at zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_leftRiemannSum_zero_of_stoppingValues
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {Y : ℕ → ℝ≥0 → Ω → ℝ} (π : ℕ → StoppingTimePartition F)
    (h0 : ∀ n, Measurable[F 0] (Y n 0))
    (hcoef : ∀ n (i : Fin (π n).size),
      Measurable[((π n).point i.castSucc).measurableSpace]
        (fun ω ↦ Y n ((π n).point i.castSucc ω) ω))
    (hu : TendstoUCP P Y atTop 0) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess (Y n) X) atTop 0 := by
  let hS n := (π n).isSimplePredictable_leftSample_of_stoppingValues (h0 n) (hcoef n)
  have hJ := hX.tendstoUCP_elementaryIntegralProcess_zero hF hS (hu.leftSampleProcess_zero π)
  have heq (n : ℕ) : (π n).leftRiemannSumProcess (Y n) X =
      fun t ω ↦ (hS n).elementaryIntegralProcess X t ω -
        (hS n).elementaryIntegralProcess X 0 ω := by
    rw [(π n).leftRiemannSumProcess_eq_elementaryIntegralProcess_sub_initial
      (h0 n) (hcoef n) (hS n) X]
    simp only [IsSimplePredictable.elementaryIntegralProcess_zero,
      StoppingTimePartition.leftSampleProcess_zero]
  convert! hJ.initialIncrement using 1 <;> simp only [heq, Pi.zero_apply, sub_self]
  rfl

theorem IsSemimartingale.tendstoUCP_leftRiemannSum_zero_of_rightContinuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {Y : ℕ → ℝ≥0 → Ω → ℝ} (π : ℕ → StoppingTimePartition F)
    (ha : ∀ n, Adapted F (Y n)) (hr : ∀ n, HasRightContinuousPaths (Y n) P)
    (hu : TendstoUCP P Y atTop 0) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess (Y n) X) atTop 0 :=
  hX.tendstoUCP_leftRiemannSum_zero_of_stoppingValues hF π (fun n ↦ ha n 0)
    (fun n i ↦ (ha n).stronglyAdapted.measurable_stoppedValue_of_usual hF (hr n)
      ((π n).point i.castSucc).isStoppingTime) hu

theorem IsSemimartingale.tendstoUCP_leftRiemannSum_zero_of_leftContinuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {Y : ℕ → ℝ≥0 → Ω → ℝ} (π : ℕ → StoppingTimePartition F)
    (ha : ∀ n, Adapted F (Y n)) (hr : ∀ n, HasLeftContinuousPaths (Y n) P)
    (hu : TendstoUCP P Y atTop 0) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess (Y n) X) atTop 0 :=
  hX.tendstoUCP_leftRiemannSum_zero_of_stoppingValues hF π (fun n ↦ ha n 0)
    (fun n i ↦ (ha n).measurable_stoppedValue_of_leftContinuous_usual hF (hr n)
      ((π n).point i.castSucc).isStoppingTime) hu

end ProbabilityTheory
