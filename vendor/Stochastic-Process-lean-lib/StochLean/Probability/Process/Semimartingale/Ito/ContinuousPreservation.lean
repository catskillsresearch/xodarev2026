/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.Continuous
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation

/-! # C2 transformations preserve continuous semimartingales

The semimartingale assertion follows from the proved Itô formula, not from
an assumed closure under nonlinear transformations. The initial random
variable is retained without integrability assumptions.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.contDiff_comp_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (hf : ContDiff ℝ 2 f) :
    IsSemimartingale (fun t ω ↦ f (X t ω)) F P := by
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
  let hr₁ := hX.hasCadlagPaths.continuous_comp hd.continuous
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
    fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
  let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
  have hJ₁ := hX.isSemimartingale_stochasticIntegral hF
    (ha₁.leftLimitProcess_of_usual hF hr₁) hr₁.hasCagladPaths_leftLimitProcess
  have hJ₂ := (hX.isSemimartingale_quadraticVariation hF).isSemimartingale_stochasticIntegral
    hF (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess
  have hC := isSemimartingale_const_initial (P := P)
    (hf.continuous.measurable.comp (hX.adapted 0))
  apply (hC.add (hJ₁.add (hJ₂.const_mul (1 / 2 : ℝ)))).congr_of_adapted _
    (fun t ↦ hf.continuous.measurable.comp (hX.adapted t))
  filter_upwards [hX.ito_of_continuous hF hc hf] with ω hω t
  have h := hω t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at h ⊢
  linarith only [h]

end ProbabilityTheory
