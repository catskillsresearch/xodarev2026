/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Basic
public import StochLean.Probability.Process.Semimartingale.Ito.VectorJumpSummability
public import StochLean.Probability.Process.Path.ComplexJump
public import StochLean.ForMathlib.Analysis.ComplexCoordinateTaylor

/-! # Absolute convergence of actual complex analytic jump corrections

The norm is controlled by the two real component corrections. Every finite
horizon is covered on one event; no integrability of initial values is used.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ}

theorem IsComplexSemimartingale.summable_norm_sq_jumps
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦ ‖complexJumpProcess Z s ω‖ ^ 2) := by
  filter_upwards [hZ.1.summable_sq_jumps hF, hZ.2.summable_sq_jumps hF] with ω hR hI t
  simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← pow_two,
    complexJumpProcess_re, complexJumpProcess_im] using (hR t).add (hI t)

theorem IsComplexSemimartingale.summable_norm_differentiable_jump_remainders
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦
      ‖f (Z s ω) - f (complexLeftLimitProcess Z s ω) -
        deriv f (complexLeftLimitProcess Z s ω) * complexJumpProcess Z s ω‖) := by
  let X : Fin 2 → ℝ≥0 → Ω → ℝ := ![fun t ω ↦ (Z t ω).re, fun t ω ↦ (Z t ω).im]
  have hX : ∀ i, IsSemimartingale (X i) F P := by
    intro i
    fin_cases i
    · exact hZ.1
    · exact hZ.2
  have he (t : ℝ≥0) (ω : Ω) : complexCoordinates (fun i ↦ X i t ω) = Z t ω := by
    apply Complex.ext <;> simp [X]
  have hl (t : ℝ≥0) (ω : Ω) :
      complexCoordinates (fun i ↦ leftLimitProcess (X i) t ω) =
        complexLeftLimitProcess Z t ω := by
    apply Complex.ext <;> simp [X, complexLeftLimitProcess, complexProcess]
  have hcomponent (L : ℂ →L[ℝ] ℝ) : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦
        |L (f (Z s ω) - f (complexLeftLimitProcess Z s ω) -
          deriv f (complexLeftLimitProcess Z s ω) * complexJumpProcess Z s ω)|) := by
    filter_upwards [summable_abs_frechet_semimartingale_jump_remainders hX hF
      (contDiff_complex_coordinate_component hf L)] with ω hω t
    have hj (s : Ioc 0 t) : (fun i ↦ jumpProcess (X i) s ω) =
        (fun i ↦ X i s ω) - (fun i ↦ leftLimitProcess (X i) s ω) := rfl
    have h := (hω t).1
    simp only [hj] at h
    simp only [complex_coordinate_first_order_remainder hf L] at h
    simpa only [he, hl, complexJumpProcess, Pi.sub_apply] using h
  filter_upwards [hcomponent Complex.reCLM, hcomponent Complex.imCLM] with ω hR hI t
  exact summable_norm_complex_of_summable_abs_components (hR t) (hI t)

end ProbabilityTheory
