/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.RightContinuousL1
public import StochLean.Probability.Process.Filtration.Usual

/-! # The necessary expectation condition for one-sided regularization

If a one-sided martingale has a right-continuous modification under a usual
filtration, its expectation function is right-continuous. Completeness first
transfers adaptedness to the modification; equality of means is then used at
deterministic times only. This does not construct the regular modification.
-/

@[expose] public section

open ProbabilityTheory
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.isRightContinuousPath_integral_of_modification
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hm : IsModification X Y P)
    (hr : HasRightContinuousPaths Y P) :
    IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  have ha : StronglyAdapted F Y := by
    intro t
    have hc : IsCompleteSubMeasurableSpace P (F t) :=
      fun A hA ↦ F.mono bot_le A (hF.complete_initial A hA)
    exact (hc.measurable_congr_ae (hX.stronglyAdapted t).measurable (hm t)).stronglyMeasurable
  have he : (fun t ↦ ∫ ω, X t ω ∂P) = (fun t ↦ ∫ ω, Y t ω ∂P) := by
    funext t
    exact integral_congr_ae (hm t)
  rw [he]
  exact (hX.congr ha hm).isRightContinuousPath_integral hr

theorem Submartingale.isRightContinuousPath_integral_of_modification
    (hX : Submartingale X F P) (hF : F.IsUsual P) (hm : IsModification X Y P)
    (hr : HasRightContinuousPaths Y P) :
    IsRightContinuousPath (fun t ↦ ∫ ω, X t ω ∂P) := by
  have ha : StronglyAdapted F Y := by
    intro t
    have hc : IsCompleteSubMeasurableSpace P (F t) :=
      fun A hA ↦ F.mono bot_le A (hF.complete_initial A hA)
    exact (hc.measurable_congr_ae (hX.stronglyAdapted t).measurable (hm t)).stronglyMeasurable
  have he : (fun t ↦ ∫ ω, X t ω ∂P) = (fun t ↦ ∫ ω, Y t ω ∂P) := by
    funext t
    exact integral_congr_ae (hm t)
  rw [he]
  exact (hX.congr ha hm).isRightContinuousPath_integral hr

end MeasureTheory
