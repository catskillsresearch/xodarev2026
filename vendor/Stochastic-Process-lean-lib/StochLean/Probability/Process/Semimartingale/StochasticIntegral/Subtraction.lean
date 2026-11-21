/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Algebra
public import StochLean.Probability.Process.Path.Subtraction

/-! # Subtraction for the source Chapter II integral -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H K : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_sub
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    Indistinguishable
      (hX.stochasticIntegral hF (fun t ↦ (haH t).sub (haK t)) (hrH.sub hrK))
      (hX.stochasticIntegral hF haH hrH - hX.stochasticIntegral hF haK hrK) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP haH hF hrH
  obtain ⟨R, hR, huR⟩ := exists_simplePredictable_tendstoUCP haK hF hrK
  apply hX.stochasticIntegral_indistinguishable_of_limit hF _ _
    (fun n ↦ (hS n).sub (hR n)) (huS.sub huR)
  · have hsub := (hX.tendstoUCP_stochasticIntegral_of_simple hF haH hrH hS huS).sub
      (hX.tendstoUCP_stochasticIntegral_of_simple hF haK hrK hR huR)
    have heq : (fun n ↦ ((hS n).sub (hR n)).elementaryIntegralProcess X) =
        fun n ↦ (hS n).elementaryIntegralProcess X - (hR n).elementaryIntegralProcess X := by
      funext n
      exact (hS n).elementaryIntegralProcess_sub (hR n) X
    rw [heq]
    exact hsub
  · exact ((hX.hasCadlagPaths_stochasticIntegral hF haH hrH).sub
      (hX.hasCadlagPaths_stochasticIntegral hF haK hrK)).hasRightContinuousPaths

end ProbabilityTheory
