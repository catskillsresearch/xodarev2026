/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Basic
public import StochLean.Probability.Process.Semimartingale.Ito.VectorPreservation
public import StochLean.ForMathlib.Analysis.ComplexCoordinateDerivatives

/-! # Analytic transformations preserve complex coordinate semimartingales

The argument applies the proved real finite-coordinate C2 theorem to the
actual real and imaginary components. No independent complex stochastic
calculus is assumed in proving preservation.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsComplexSemimartingale.differentiable_comp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ} {f : ℂ → ℂ}
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (hf : Differentiable ℂ f) :
    IsComplexSemimartingale (fun t ω ↦ f (Z t ω)) F P := by
  let X : Fin 2 → ℝ≥0 → Ω → ℝ := ![fun t ω ↦ (Z t ω).re, fun t ω ↦ (Z t ω).im]
  have hX : ∀ i, IsSemimartingale (X i) F P := by
    intro i
    fin_cases i
    · exact hZ.1
    · exact hZ.2
  have he (t : ℝ≥0) (ω : Ω) : complexCoordinates (fun i ↦ X i t ω) = Z t ω := by
    apply Complex.ext <;> simp [X]
  constructor
  · simpa only [he, Complex.reCLM_apply] using
      isSemimartingale_contDiff_comp_finiteCoordinates hX hF
        (contDiff_complex_coordinate_component hf Complex.reCLM)
  · simpa only [he, Complex.imCLM_apply] using
      isSemimartingale_contDiff_comp_finiteCoordinates hX hF
        (contDiff_complex_coordinate_component hf Complex.imCLM)

end ProbabilityTheory
