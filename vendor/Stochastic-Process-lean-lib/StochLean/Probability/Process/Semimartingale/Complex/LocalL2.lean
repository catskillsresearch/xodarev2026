/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Integral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalL2
public import StochLean.Probability.Process.LocalMartingale.Complex

/-! # Complex integrands preserve the real integrator's local L2 martingale property -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.isComplexLocalMartingale_complexIntegrandIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F]
    {X : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsComplexLocalMartingale (hX.complexIntegrandIntegral hF ha hr) F P :=
  ⟨hX.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable hF hL
      (fun t ↦ Complex.continuous_re.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_re),
    hX.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable hF hL
      (fun t ↦ Complex.continuous_im.measurable.comp (ha t))
      (hr.continuous_comp Complex.continuous_im)⟩

end ProbabilityTheory
