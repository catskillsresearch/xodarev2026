/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrationByParts
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Algebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalMartingale

/-! # Products compensated by raw covariation for general local martingales

The full local-martingale preservation theorem for the existing stochastic
integral removes the earlier locally-square-integrable hypotheses from the
product-minus-covariation conclusion. Integration by parts identifies the
sum of the two actual integrals with that process on one common event.

The square conclusion follows from the established diagonal identity for
the same raw covariation, without another bracket definition or a repeated
construction of its algebra. The raw owners retain their initial product
and square. Consequently no integrability, square integrability, or zero
condition on either original initial value is required.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M N : ℝ≥0 → Ω → ℝ}

/-- The product of two arbitrary native local martingales, less their actual
raw covariation, is a local martingale. No local L2 or initial moment is assumed. -/
theorem IsLocalMartingale.isLocalMartingale_mul_sub_quadraticCovariation
    (hM : IsLocalMartingale M F P) (hN : IsLocalMartingale N F P) (hF : F.IsUsual P) :
    IsLocalMartingale
      (M * N - (hM.isSemimartingale hF).quadraticCovariation (hN.isSemimartingale hF) hF)
      F P := by
  let hSM := hM.isSemimartingale hF
  let hSN := hN.isSemimartingale hF
  have hJN := hSN.isLocalMartingale_stochasticIntegral hF hN
    (hSM.adapted.leftLimitProcess_of_usual hF hSM.hasCadlagPaths)
    hSM.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hJM := hSM.isLocalMartingale_stochasticIntegral hF hM
    (hSN.adapted.leftLimitProcess_of_usual hF hSN.hasCadlagPaths)
    hSN.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  apply (hJN.add hJM hF).congr hF
    (fun t ↦ ((hSM.adapted t).mul (hSN.adapted t)).sub
      (hSM.adapted_quadraticCovariation hSN hF t))
  filter_upwards [hSM.quadraticCovariation_eq_product_sub_integrals hSN hF] with ω hω t
  simp only [Pi.sub_apply, Pi.add_apply, hω t, Pi.mul_apply]
  ring

/-- A general native local martingale squared, less its actual raw quadratic
variation, is local. The diagonal raw-covariation identity supplies the result
without imposing an initial square-integrability or zero-initial hypothesis. -/
theorem IsLocalMartingale.isLocalMartingale_sq_sub_quadraticVariation
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P) :
    IsLocalMartingale
      (fun t ω ↦ (M t ω) ^ 2 - (hM.isSemimartingale hF).quadraticVariation hF t ω) F P := by
  let hSM := hM.isSemimartingale hF
  apply (hM.isLocalMartingale_mul_sub_quadraticCovariation hM hF).congr hF
    (fun t ↦ ((hM.1 t).pow_const 2).sub (hSM.adapted_quadraticVariation hF t))
  filter_upwards [hSM.quadraticCovariation_self hF] with ω hω t
  simp only [Pi.sub_apply, Pi.mul_apply, hω t, pow_two]

end ProbabilityTheory
