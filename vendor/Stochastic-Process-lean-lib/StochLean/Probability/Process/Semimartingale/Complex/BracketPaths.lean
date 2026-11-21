/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.QuadraticVariation

/-! # Continuity of the complex bilinear continuous bracket -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ}

theorem IsComplexSemimartingale.continuous_continuousQuadraticVariation
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (ω : Ω) :
    Continuous (hZ.continuousQuadraticVariation hF · ω) := by
  have hR := (hZ.1.continuous_continuousQuadraticVariation hF ω).sub
    (hZ.2.continuous_continuousQuadraticVariation hF ω)
  have hI := (hZ.1.continuous_continuousQuadraticCovariation hZ.2 hF ω).const_mul 2
  convert (Complex.continuous_ofReal.comp hR).add
    ((Complex.continuous_ofReal.comp hI).const_mul Complex.I) using 1
  funext t
  apply Complex.ext <;> simp [continuousQuadraticVariation, complexProcess]

theorem IsComplexSemimartingale.hasContinuousPaths_continuousQuadraticVariation
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    HasContinuousPaths (hZ.continuousQuadraticVariation hF) P :=
  Filter.Eventually.of_forall (hZ.continuous_continuousQuadraticVariation hF)

end ProbabilityTheory
