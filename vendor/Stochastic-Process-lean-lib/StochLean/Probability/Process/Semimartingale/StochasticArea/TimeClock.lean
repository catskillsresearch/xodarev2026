/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.Characteristic
public import StochLean.Probability.Brownian.LevyCharacterization

/-! # Levy's stochastic-area formula for the standard time clock

The clock, its regularity, and the zero initial values are discharged from
the raw bracket hypotheses. Only orthogonality and the two continuous local
martingales remain as inputs; in particular no area law is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsContinuousLocalMartingale.integral_exp_stochasticArea_eq_inv_cosh_time
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsContinuousLocalMartingale X F P) (hY : IsContinuousLocalMartingale Y F P)
    (hF : F.IsUsual P)
    (hqX : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (hqY : Indistinguishable ((hY.isSemimartingale hF).quadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (ho : Indistinguishable
      ((hX.isSemimartingale hF).continuousQuadraticCovariation (hY.isSemimartingale hF) hF) 0 P)
    (u : ℝ) (S : ℝ≥0) :
    (∫ ω, Complex.exp (Complex.I * (u : ℂ) *
      ((hX.isSemimartingale hF).stochasticArea (hY.isSemimartingale hF) hF S ω : ℂ)) ∂P) =
        ((Real.cosh (u * S))⁻¹ : ℂ) := by
  have hc : HasContinuousPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) P :=
    Filter.Eventually.of_forall fun _ ↦ NNReal.continuous_coe
  have hv : HasFiniteVariationPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) P :=
    (show HasMonotonePaths (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) P from
      Filter.Eventually.of_forall (fun _ _ _ h ↦ NNReal.coe_le_coe.mpr h)).hasFiniteVariationPaths
  have hQ := hv.isSemimartingale (fun _ ↦ measurable_const) hF hc.hasCadlagPaths
  exact hX.integral_exp_stochasticArea_eq_inv_cosh hY hQ hF hqX hqY ho hv hc
    (hX.isBrownianReal_of_quadraticVariation_eq_time hF hqX).eval_zero_ae_eq_zero
    (hY.isBrownianReal_of_quadraticVariation_eq_time hF hqY).eval_zero_ae_eq_zero
    (Filter.Eventually.of_forall fun _ ↦ rfl) u S S
    (Filter.Eventually.of_forall fun _ ↦ rfl)

end ProbabilityTheory
