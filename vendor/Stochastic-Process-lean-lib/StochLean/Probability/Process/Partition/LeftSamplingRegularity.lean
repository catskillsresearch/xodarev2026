/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.LeftSampling
public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessRegularity
public import StochLean.Probability.Process.Path.Subtraction

/-! # Adaptedness and cadlag paths of increment-only random Riemann sums

These properties follow from the existing source representation and its
independent initial term. The integrator need not be a semimartingale.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {Y X : ℝ≥0 → Ω → ℝ}

theorem leftRiemannSumProcess_eq_elementaryIntegralProcess_sub_initial
    (π : StoppingTimePartition F) (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω))
    (hS : IsSimplePredictable (π.leftSampleProcess Y) F) (X : ℝ≥0 → Ω → ℝ) :
    π.leftRiemannSumProcess Y X = fun t ω ↦ hS.elementaryIntegralProcess X t ω - Y 0 ω * X 0 ω := by
  rw [hS.elementaryIntegralProcess_eq _ (π.toProcess_leftSampleRep Y h0 hcoef) X]
  exact π.leftRiemannSumProcess_eq_integralProcess_sub_initial Y X h0 hcoef

theorem adapted_leftRiemannSumProcess (π : StoppingTimePartition F)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω))
    (haX : Adapted F X) (hF : F.IsUsual P) (hrX : HasRightContinuousPaths X P) :
    Adapted F (π.leftRiemannSumProcess Y X) := by
  rw [π.leftRiemannSumProcess_eq_integralProcess_sub_initial Y X h0 hcoef]
  intro t
  exact ((π.leftSampleRep Y h0 hcoef).adapted_integralProcess haX hF hrX t).sub
    ((h0.mul (haX 0)).mono (F.mono bot_le) le_rfl)

theorem hasCadlagPaths_leftRiemannSumProcess (π : StoppingTimePartition F)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω))
    (hrX : HasCadlagPaths X P) : HasCadlagPaths (π.leftRiemannSumProcess Y X) P := by
  rw [π.leftRiemannSumProcess_eq_integralProcess_sub_initial Y X h0 hcoef]
  exact ((π.leftSampleRep Y h0 hcoef).hasCadlagPaths_integralProcess hrX).sub
    (ae_of_all _ fun _ ↦ IsContinuousPath.isCadlagPath continuous_const)

end ProbabilityTheory.StoppingTimePartition
