/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.SemimartingaleCovariation
public import StochLean.Probability.Brownian.FiltrationMartingale
public import StochLean.Probability.Process.Semimartingale.StochasticArea.Density

/-! # Levy's area characteristic function for independent Brownian motions

The canonical Brownian predicates and whole-process independence imply the
bracket inputs; independence of each future increment from the chosen past
supplies the two local martingales. The filtration conditions are explicit:
Brownian path laws alone do not imply a martingale under an enlarged filtration.
The area is the source twice-signed area, with no extra factor one half.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsBrownianReal.integral_exp_stochasticArea_eq_inv_cosh
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsBrownianReal X P) (hY : IsBrownianReal Y P) (hF : F.IsUsual P)
    (haX : Adapted F X) (haY : Adapted F Y)
    (hpX : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hpY : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ Y t ω - Y s ω) inferInstance) P)
    (hi : IndepFun (fun ω t ↦ X t ω) (fun ω t ↦ Y t ω) P) (u : ℝ) (S : ℝ≥0) :
    let hMX := hX.isContinuousLocalMartingale_of_indep_past haX hpX
    let hMY := hY.isContinuousLocalMartingale_of_indep_past haY hpY
    (∫ ω, Complex.exp (Complex.I * (u : ℂ) *
      ((hMX.isSemimartingale hF).stochasticArea (hMY.isSemimartingale hF) hF S ω : ℂ)) ∂P) =
        ((Real.cosh (u * S))⁻¹ : ℂ) := by
  let hMX := hX.isContinuousLocalMartingale_of_indep_past haX hpX
  let hMY := hY.isContinuousLocalMartingale_of_indep_past haY hpY
  exact hMX.integral_exp_stochasticArea_eq_inv_cosh_time hMY hF
    (hX.quadraticVariation_eq_time_of_semimartingale (hMX.isSemimartingale hF) hF)
    (hY.quadraticVariation_eq_time_of_semimartingale (hMY.isSemimartingale hF) hF)
    (hX.continuousQuadraticCovariation_eq_zero_of_indep hY hi
      (hMX.isSemimartingale hF) (hMY.isSemimartingale hF) hF) u S

theorem IsBrownianReal.hasLaw_stochasticArea
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsBrownianReal X P) (hY : IsBrownianReal Y P) (hF : F.IsUsual P)
    (haX : Adapted F X) (haY : Adapted F Y)
    (hpX : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hpY : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ Y t ω - Y s ω) inferInstance) P)
    (hi : IndepFun (fun ω t ↦ X t ω) (fun ω t ↦ Y t ω) P) (S : ℝ≥0) :
    let hMX := hX.isContinuousLocalMartingale_of_indep_past haX hpX
    let hMY := hY.isContinuousLocalMartingale_of_indep_past haY hpY
    HasLaw ((hMX.isSemimartingale hF).stochasticArea (hMY.isSemimartingale hF) hF S)
      (hyperbolicSecantMeasure S) P := by
  let hMX := hX.isContinuousLocalMartingale_of_indep_past haX hpX
  let hMY := hY.isContinuousLocalMartingale_of_indep_past haY hpY
  have hA := (hMX.isSemimartingale hF).isSemimartingale_stochasticArea (hMY.isSemimartingale hF) hF
  exact hasLaw_hyperbolicSecant_of_integral_exp hA.adapted.measurable.aemeasurable S
    (fun u ↦ hX.integral_exp_stochasticArea_eq_inv_cosh hY hF haX haY hpX hpY hi u S)

theorem IsBrownianReal.map_stochasticArea_eq_withDensity
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsBrownianReal X P) (hY : IsBrownianReal Y P) (hF : F.IsUsual P)
    (haX : Adapted F X) (haY : Adapted F Y)
    (hpX : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (hpY : ∀ s t, s ≤ t → Indep (F s)
      (MeasurableSpace.comap (fun ω ↦ Y t ω - Y s ω) inferInstance) P)
    (hi : IndepFun (fun ω t ↦ X t ω) (fun ω t ↦ Y t ω) P) {S : ℝ≥0} (hS : S ≠ 0) :
    let hMX := hX.isContinuousLocalMartingale_of_indep_past haX hpX
    let hMY := hY.isContinuousLocalMartingale_of_indep_past haY hpY
    P.map ((hMX.isSemimartingale hF).stochasticArea (hMY.isSemimartingale hF) hF S) =
      volume.withDensity (fun x : ℝ ↦
        ENNReal.ofReal ((2 * S * Real.cosh (Real.pi * x / (2 * S)))⁻¹)) := by
  exact (hX.hasLaw_stochasticArea hY hF haX haY hpX hpY hi S).map_eq.trans
    (hyperbolicSecantMeasure_of_ne_zero hS)

end ProbabilityTheory
