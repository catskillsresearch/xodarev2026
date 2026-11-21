/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Integral
public import StochLean.Analysis.PathVariation.StieltjesIntegralRegularity
public import StochLean.Probability.Process.Semimartingale.FiniteVariation

/-! # Regularity and semimartingale property of pathwise FV integrals

The local integrability condition holds on one common event. No expectation of
variation or of the initial value is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {X H : ℝ≥0 → Ω → ℝ}
  {hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ}
  {hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)} {P : Measure Ω}

theorem hasCadlagPaths_finiteVariationIntegral
    (hH : ∀ᵐ ω ∂P, ∀ T, IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure) :
    HasCadlagPaths (finiteVariationIntegral X hv hr H) P :=
  hH.mono fun _ hω ↦ isCadlagPath_pathStieltjesIntegral hω

theorem hasFiniteVariationPaths_finiteVariationIntegral
    (hH : ∀ᵐ ω ∂P, ∀ T, IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure) :
    HasFiniteVariationPaths (finiteVariationIntegral X hv hr H) P :=
  hH.mono fun _ hω ↦ locallyBoundedVariationOn_pathStieltjesIntegral hω

theorem isSemimartingale_finiteVariationIntegral [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} (ha : Adapted F X) (hF : F.IsUsual P)
    (hHp : IsStronglyProgressive F H)
    (hH : ∀ᵐ ω ∂P, ∀ T, IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure) :
    IsSemimartingale (finiteVariationIntegral X hv hr H) F P :=
  (hasFiniteVariationPaths_finiteVariationIntegral hH).isSemimartingale
    (adapted_finiteVariationIntegral X hv hr ha hHp) hF
    (hasCadlagPaths_finiteVariationIntegral hH)

end ProbabilityTheory
