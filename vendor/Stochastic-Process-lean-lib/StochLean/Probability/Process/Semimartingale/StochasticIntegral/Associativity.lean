/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation

/-! # Protter II.19: associativity on the Chapter II domain

Both adapted integrands have common-event caglad paths. The inner integral is
proved to be a semimartingale before the outer general integral is selected.
Associativity is an indistinguishability identity, including its initial term.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X G H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haG : Adapted F G) (hrG : HasCagladPaths G P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF haH hrH).stochasticIntegral hF haG hrG)
      (hX.stochasticIntegral hF (fun t ↦ (haG t).mul (haH t)) (hrG.mul hrH)) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP haG hF hrG
  have hY := hX.isSemimartingale_stochasticIntegral hF haH hrH
  have huLeft := hY.tendstoUCP_stochasticIntegral_of_simple hF haG hrG hS huS
  have huProduct := huS.mul_right_of_caglad
    (fun n t ↦ ((hS n).adapted t).mono (F.le t) le_rfl)
    (fun t ↦ (haG t).mono (F.le t) le_rfl)
    (fun t ↦ (haH t).mono (F.le t) le_rfl)
    (fun n ↦ (hS n).hasCagladPaths P) hrG hrH
  have huRight := hX.tendstoUCP_stochasticIntegral hF
    (fun t ↦ (haG t).mul (haH t)) (hrG.mul hrH)
    (fun n t ↦ ((hS n).adapted t).mul (haH t))
    (fun n ↦ ((hS n).hasCagladPaths P).mul hrH) huProduct
  have huIdentified := huLeft.congr_left (fun n ↦
    hX.elementaryIntegralProcess_stochasticIntegral hF (hS n) haH hrH)
  exact huIdentified.indistinguishable_unique huRight
    (hY.hasCadlagPaths_stochasticIntegral hF haG hrG).hasRightContinuousPaths
    (hX.hasCadlagPaths_stochasticIntegral hF _ _).hasRightContinuousPaths

end ProbabilityTheory
