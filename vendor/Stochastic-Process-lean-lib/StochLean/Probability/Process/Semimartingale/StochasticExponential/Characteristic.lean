/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Continuous
public import StochLean.Probability.Process.Semimartingale.Complex.Preservation

/-! # The compensated characteristic exponential

The real compensation is positive: its imaginary coefficient has negative
bilinear quadratic variation. This is a function of the existing continuous
real bracket, not a second stochastic integration or bracket construction.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.characteristicExponent
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) : ℝ≥0 → Ω → ℂ :=
  complexProcess (fun t ω ↦ ((1 / 2 : ℝ) * u ^ 2) * hX.continuousQuadraticVariation hF t ω)
    (fun t ω ↦ u * X t ω)

noncomputable def IsSemimartingale.characteristicExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) : ℝ≥0 → Ω → ℂ :=
  fun t ω ↦ Complex.exp (hX.characteristicExponent hF u t ω)

theorem IsSemimartingale.isComplexSemimartingale_characteristicExponent
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) :
    IsComplexSemimartingale (hX.characteristicExponent hF u) F P :=
  ((hX.isSemimartingale_continuousQuadraticVariation hF).const_mul ((1 / 2) * u ^ 2)).complex
    (hX.const_mul u)

theorem IsSemimartingale.isComplexSemimartingale_characteristicExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) :
    IsComplexSemimartingale (hX.characteristicExponential hF u) F P :=
  (hX.isComplexSemimartingale_characteristicExponent hF u).differentiable_comp
    hF Complex.differentiable_exp

theorem IsSemimartingale.hasContinuousPaths_characteristicExponent
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) (u : ℝ) :
    HasContinuousPaths (hX.characteristicExponent hF u) P := by
  filter_upwards [hc] with ω hx
  have hQ := (hX.continuous_continuousQuadraticVariation hF ω).const_mul ((1 / 2) * u ^ 2)
  have hU := hx.const_mul u
  have h := (Complex.continuous_ofReal.comp hQ).add
    ((continuous_const : Continuous (fun _ : ℝ≥0 ↦ Complex.I)).mul
      (Complex.continuous_ofReal.comp hU))
  apply h.congr
  intro t
  apply Complex.ext <;> simp [characteristicExponent, complexProcess, pow_two]

theorem IsSemimartingale.hasContinuousPaths_characteristicExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) (u : ℝ) :
    HasContinuousPaths (hX.characteristicExponential hF u) P :=
  (hX.hasContinuousPaths_characteristicExponent hF hc u).mono
    (fun _ h ↦ Complex.continuous_exp.comp h)

theorem IsSemimartingale.norm_characteristicExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) (t : ℝ≥0) (ω : Ω) :
    ‖hX.characteristicExponential hF u t ω‖ =
      Real.exp (((1 / 2 : ℝ) * u ^ 2) * hX.continuousQuadraticVariation hF t ω) := by
  simp only [characteristicExponential, Complex.norm_exp, characteristicExponent, complexProcess]

theorem IsSemimartingale.characteristicExponential_zero_ae
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) (h0 : X 0 =ᵐ[P] 0) :
    hX.characteristicExponential hF u 0 =ᵐ[P] 1 := by
  filter_upwards [h0] with ω hz
  simp only [characteristicExponential, characteristicExponent, complexProcess, hz,
    continuousQuadraticVariation_zero, Pi.zero_apply, mul_zero, Pi.one_apply]
  change Complex.exp 0 = 1
  exact Complex.exp_zero

end ProbabilityTheory
