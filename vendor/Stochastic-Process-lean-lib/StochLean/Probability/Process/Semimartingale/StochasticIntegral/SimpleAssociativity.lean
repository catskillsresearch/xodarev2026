/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Associativity
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegratorContinuity
public import StochLean.Probability.Process.UCP.Multiplication

/-! # Associativity with a simple outer integrand

The inner integral is the actual Chapter II extension. Its semimartingale
property is not assumed here: this result is used to prove that property.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X G H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.elementaryIntegralProcess_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hG : IsSimplePredictable G F) (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable (hG.elementaryIntegralProcess (hX.stochasticIntegral hF ha hr))
      (hX.stochasticIntegral hF (fun t ↦ (hG.adapted t).mul (ha t))
        ((hG.hasCagladPaths P).mul hr)) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  have huJ := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  have huOuter := hG.tendstoUCP_elementaryIntegralProcess_integrator hF
    (fun n ↦ (hS n).adapted_elementaryIntegralProcess hX.adapted hF
      hX.hasCadlagPaths.hasRightContinuousPaths)
    (hX.adapted_stochasticIntegral hF ha hr)
    (fun n ↦ (hS n).hasCadlagPaths_elementaryIntegralProcess hX.hasCadlagPaths)
    (hX.hasCadlagPaths_stochasticIntegral hF ha hr) huJ
  have huProd := huS.mul_left_of_caglad
    (fun n t ↦ ((hS n).adapted t).mono (F.le t) le_rfl)
    (fun t ↦ (ha t).mono (F.le t) le_rfl)
    (fun t ↦ (hG.adapted t).mono (F.le t) le_rfl)
    (fun n ↦ (hS n).hasCagladPaths P) hr (hG.hasCagladPaths P)
  have huProdJ := hX.tendstoUCP_stochasticIntegral_of_simple hF
    (fun t ↦ (hG.adapted t).mul (ha t)) ((hG.hasCagladPaths P).mul hr)
    (fun n ↦ hG.mul (hS n)) huProd
  have heq : (fun n ↦ hG.elementaryIntegralProcess ((hS n).elementaryIntegralProcess X)) =
      fun n ↦ (hG.mul (hS n)).elementaryIntegralProcess X := by
    funext n
    exact hG.elementaryIntegralProcess_elementaryIntegralProcess (hS n) X
  rw [heq] at huOuter
  exact huOuter.indistinguishable_unique huProdJ
    (hG.hasCadlagPaths_elementaryIntegralProcess
      (hX.hasCadlagPaths_stochasticIntegral hF ha hr)).hasRightContinuousPaths
    (hX.hasCadlagPaths_stochasticIntegral hF _ _).hasRightContinuousPaths

end ProbabilityTheory
