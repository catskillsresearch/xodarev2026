/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.TimeClock
public import StochLean.Probability.Distributions.HyperbolicSecant

/-! # The actual stochastic-area law and its positive-time density

Fourier uniqueness identifies the existing stochastic area with the proved
hyperbolic-secant probability measure. The zero-safe law holds at every time;
the Lebesgue-density conclusion has an explicit nonzero-time guard.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Y : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.hasLaw_stochasticArea
    (hX : IsContinuousLocalMartingale X F P) (hY : IsContinuousLocalMartingale Y F P)
    (hF : F.IsUsual P)
    (hqX : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (hqY : Indistinguishable ((hY.isSemimartingale hF).quadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (ho : Indistinguishable
      ((hX.isSemimartingale hF).continuousQuadraticCovariation (hY.isSemimartingale hF) hF) 0 P)
    (S : ℝ≥0) :
    HasLaw ((hX.isSemimartingale hF).stochasticArea (hY.isSemimartingale hF) hF S)
      (hyperbolicSecantMeasure S) P := by
  have hA := (hX.isSemimartingale hF).isSemimartingale_stochasticArea (hY.isSemimartingale hF) hF
  exact hasLaw_hyperbolicSecant_of_integral_exp hA.adapted.measurable.aemeasurable S
    (fun u ↦ hX.integral_exp_stochasticArea_eq_inv_cosh_time hY hF hqX hqY ho u S)

theorem IsContinuousLocalMartingale.map_stochasticArea_eq_withDensity
    (hX : IsContinuousLocalMartingale X F P) (hY : IsContinuousLocalMartingale Y F P)
    (hF : F.IsUsual P)
    (hqX : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (hqY : Indistinguishable ((hY.isSemimartingale hF).quadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P)
    (ho : Indistinguishable
      ((hX.isSemimartingale hF).continuousQuadraticCovariation (hY.isSemimartingale hF) hF) 0 P)
    {S : ℝ≥0} (hS : S ≠ 0) :
    P.map ((hX.isSemimartingale hF).stochasticArea (hY.isSemimartingale hF) hF S) =
      volume.withDensity (fun x : ℝ ↦
        ENNReal.ofReal ((2 * S * Real.cosh (Real.pi * x / (2 * S)))⁻¹)) := by
  exact (hX.hasLaw_stochasticArea hY hF hqX hqY ho S).map_eq.trans
    (hyperbolicSecantMeasure_of_ne_zero hS)

end ProbabilityTheory
