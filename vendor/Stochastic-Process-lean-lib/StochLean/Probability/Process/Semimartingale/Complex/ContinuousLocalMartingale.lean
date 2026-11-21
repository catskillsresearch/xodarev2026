/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.LocalL2
public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale

/-! # Complex integrands against continuous real local martingales

The existing localization theorem proves local square integrability; it is
not an additional hypothesis. The coordinate integral then preserves the
existing masked local-martingale predicates.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsContinuousLocalMartingale.isComplexLocalMartingale_complexIntegrandIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F]
    {X : ℝ≥0 → Ω → ℝ} {H : ℝ≥0 → Ω → ℂ}
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsComplexLocalMartingale ((hX.isSemimartingale hF).complexIntegrandIntegral hF ha hr) F P :=
  (hX.isSemimartingale hF).isComplexLocalMartingale_complexIntegrandIntegral hF
    (hX.locally_squareIntegrableMartingale hF) ha hr

end ProbabilityTheory
