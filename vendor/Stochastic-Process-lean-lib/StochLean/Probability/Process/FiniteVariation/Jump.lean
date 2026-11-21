/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CagladIntegral
public import StochLean.Analysis.PathVariation.StieltjesIntegralJump
public import StochLean.Probability.Process.Path.LeftLimit

/-! # Source jumps of finite-variation integrals, including time zero -/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) {H : ℝ≥0 → Ω → ℝ}

theorem jumpProcess_finiteVariationIntegral (ω : Ω)
    (hH : ∀ T, IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure) (t : ℝ≥0) :
    jumpProcess (finiteVariationIntegral X hv hr H) t ω = H t ω * jumpProcess X t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [jumpProcess_zero]
    exact finiteVariationIntegral_zero X hv hr H ω
  · change finiteVariationIntegral X hv hr H t ω -
      leftLimitProcess (finiteVariationIntegral X hv hr H) t ω =
        H t ω * (X t ω - leftLimitProcess X t ω)
    simp only [leftLimitProcess, if_neg ht]
    exact pathStieltjesIntegral_sub_leftLim hH (lt_of_le_of_ne bot_le (Ne.symm ht))

theorem jumpProcess_finiteVariationIntegral_of_caglad {F : Filtration ℝ≥0 mΩ}
    (hHa : Adapted F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω)) (t : ℝ≥0) (ω : Ω) :
    jumpProcess (finiteVariationIntegral X hv hr H) t ω = H t ω * jumpProcess X t ω :=
  jumpProcess_finiteVariationIntegral X hv hr ω
    (fun T ↦ integrableOn_variationStieltjes_of_adapted_caglad X hv hr hHa hHc T ω) t

theorem ae_jumpProcess_finiteVariationIntegral {P : Measure Ω}
    (hH : ∀ᵐ ω ∂P, ∀ T, IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure) :
    ∀ᵐ ω ∂P, ∀ t, jumpProcess (finiteVariationIntegral X hv hr H) t ω =
      H t ω * jumpProcess X t ω :=
  hH.mono fun ω hω t ↦ jumpProcess_finiteVariationIntegral X hv hr ω hω t

end ProbabilityTheory
