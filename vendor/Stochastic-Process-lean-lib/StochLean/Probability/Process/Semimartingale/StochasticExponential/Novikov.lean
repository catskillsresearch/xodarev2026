/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Kazamaki

/-! # Novikov's criterion

This file closes Protter III.45.  The bracket hypothesis is stated uniformly
over bounded stopping times, so the half-line theorem does not totalize a
quadratic variation at infinity.  Protter III.43 converts it to Kazamaki's
hypothesis, and III.44 supplies uniform integrability.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
  [IsProbabilityMeasure P] [SigmaFiniteFiltration P F]

/-- Protter III.45 (Novikov): uniform half-bracket exponential control over
bounded stopping times makes the stochastic exponential a uniformly
integrable martingale. -/
theorem IsContinuousLocalMartingale.isUIMartingale_stochasticExponential_of_novikov
    (hM : IsContinuousLocalMartingale M F P) (hF : F.IsUsual P)
    (h0 : M 0 =ᵐ[P] 0) {C : ℝ≥0} (hN : HasNovikovBound hM hF C) :
    IsUIMartingale ((hM.isSemimartingale hF).stochasticExponential hF) F P := by
  exact hM.isUIMartingale_stochasticExponential_of_kazamaki hF h0
    (HasNovikovBound.hasKazamakiBound hM hF h0 hN)

end ProbabilityTheory
