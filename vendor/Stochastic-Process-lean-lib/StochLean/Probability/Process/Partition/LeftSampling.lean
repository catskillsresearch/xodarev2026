/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Regularity
public import StochLean.Probability.Process.Stopping.LeftContinuousSampling
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual

/-! # Left sampling and increment-only Riemann sums on random partitions

The sampled process reuses the deterministic left-step owner pathwise. Its
initial value is the original initial value. The Riemann sum, in contrast,
contains only increments, so its formula subtracts the source initial product.
Repeated endpoints and arbitrary finite stopping endpoints remain legal.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def leftSampleProcess (π : StoppingTimePartition F) (Y : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ (π.path ω).leftStep (Y · ω) t

@[simp] theorem leftSampleProcess_zero (π : StoppingTimePartition F)
    (Y : ℝ≥0 → Ω → ℝ) : π.leftSampleProcess Y 0 = Y 0 := by
  funext ω
  exact (π.path ω).leftStep_zero _

noncomputable def leftSampleRep (π : StoppingTimePartition F) (Y : ℝ≥0 → Ω → ℝ)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    SimplePredictableRep F where
  partition := π
  initial := Y 0
  measurable_initial := h0
  coefficient := fun i ω ↦ Y (π.point i.castSucc ω) ω
  measurable_coefficient := hcoef

theorem toProcess_leftSampleRep (π : StoppingTimePartition F) (Y : ℝ≥0 → Ω → ℝ)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    (π.leftSampleRep Y h0 hcoef).toProcess = π.leftSampleProcess Y := by
  classical
  funext t ω
  simp only [SimplePredictableRep.toProcess, leftSampleRep, leftSampleProcess,
    StochLean.TimePartition.leftStep, Set.indicator_apply, mem_Ioc]
  rfl

theorem isSimplePredictable_leftSample_of_stoppingValues (π : StoppingTimePartition F)
    {Y : ℝ≥0 → Ω → ℝ} (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    IsSimplePredictable (π.leftSampleProcess Y) F :=
  ⟨π.leftSampleRep Y h0 hcoef, π.toProcess_leftSampleRep Y h0 hcoef⟩

theorem isSimplePredictable_leftSample_of_rightContinuous (π : StoppingTimePartition F)
    {P : Measure Ω} {Y : ℝ≥0 → Ω → ℝ} (ha : Adapted F Y) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths Y P) : IsSimplePredictable (π.leftSampleProcess Y) F :=
  π.isSimplePredictable_leftSample_of_stoppingValues (ha 0) fun i ↦
    ha.stronglyAdapted.measurable_stoppedValue_of_usual hF hr (π.point i.castSucc).isStoppingTime

theorem isSimplePredictable_leftSample_of_leftContinuous (π : StoppingTimePartition F)
    {P : Measure Ω} {Y : ℝ≥0 → Ω → ℝ} (ha : Adapted F Y) (hF : F.IsUsual P)
    (hl : HasLeftContinuousPaths Y P) : IsSimplePredictable (π.leftSampleProcess Y) F :=
  π.isSimplePredictable_leftSample_of_stoppingValues (ha 0) fun i ↦
    ha.measurable_stoppedValue_of_leftContinuous_usual hF hl (π.point i.castSucc).isStoppingTime

def leftRiemannSumProcess (π : StoppingTimePartition F) (Y X : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑ i : Fin π.size,
      Y (π.point i.castSucc ω) ω *
        (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω)

@[simp] theorem leftRiemannSumProcess_zero (π : StoppingTimePartition F)
    (Y X : ℝ≥0 → Ω → ℝ) : π.leftRiemannSumProcess Y X 0 = 0 := by
  funext ω
  simp [leftRiemannSumProcess]

theorem leftRiemannSumProcess_eq_integralProcess_sub_initial
    (π : StoppingTimePartition F) (Y X : ℝ≥0 → Ω → ℝ)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω)) :
    π.leftRiemannSumProcess Y X = fun t ω ↦
      (π.leftSampleRep Y h0 hcoef).integralProcess X t ω - Y 0 ω * X 0 ω := by
  funext t ω
  rw [SimplePredictableRep.integralProcess_apply]
  change _ = Y 0 ω * X 0 ω + π.leftRiemannSumProcess Y X t ω - Y 0 ω * X 0 ω
  ring

end ProbabilityTheory.StoppingTimePartition
