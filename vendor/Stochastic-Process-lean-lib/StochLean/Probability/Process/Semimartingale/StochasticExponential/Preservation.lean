/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Adapted
public import StochLean.Probability.Process.Semimartingale.StochasticExponential.ProductVariation
public import StochLean.Probability.Process.Semimartingale.Ito.Preservation

/-! # The product-defined stochastic exponential is a semimartingale

General cadlag adaptedness and finite variation of the product factor
are proved prerequisites. C2 preservation and multiplication then give
semimartingale regularity of the same canonical expression. This result
does not yet assert its stochastic equation or uniqueness.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.isSemimartingale_stochasticExponentialJumpProduct
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (stochasticExponentialJumpProduct X) F P :=
  (hX.hasFiniteVariationPaths_stochasticExponentialJumpProduct hF).isSemimartingale
    (hX.adapted_stochasticExponentialJumpProduct hF) hF
    (hX.hasCadlagPaths_stochasticExponentialJumpProduct hF)

theorem IsSemimartingale.isSemimartingale_stochasticExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.stochasticExponential hF) F P := by
  have hK := hX.sub ((hX.isSemimartingale_continuousQuadraticVariation hF).const_mul (1 / 2))
  exact (hK.contDiff_comp hF Real.contDiff_exp).mul
    (hX.isSemimartingale_stochasticExponentialJumpProduct hF) hF

end ProbabilityTheory
