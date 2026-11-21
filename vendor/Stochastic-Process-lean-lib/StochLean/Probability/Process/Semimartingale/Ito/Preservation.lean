/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.RawBracket
public import StochLean.Probability.Process.Semimartingale.Ito.JumpVariation
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation

/-! # C2 transformations preserve general cadlag semimartingales

The residual is adapted and cadlag before semimartingale preservation is
claimed. The proved raw Ito identity identifies that residual with the
actual finite-variation jump series. This supplies its good-integrator
property without assuming nonlinear closure or a classical decomposition.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.contDiff_comp
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    IsSemimartingale (fun t ω ↦ f (X t ω)) F P := by
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
  let hr₁ := hX.hasCadlagPaths.continuous_comp hd.continuous
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
    fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
  let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
  let J₁ := hX.stochasticIntegral hF
    (ha₁.leftLimitProcess_of_usual hF hr₁) hr₁.hasCagladPaths_leftLimitProcess
  let J₂ := (1 / 2 : ℝ) • (hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF
    (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess
  have hJ₁ : IsSemimartingale J₁ F P := hX.isSemimartingale_stochasticIntegral hF
    (ha₁.leftLimitProcess_of_usual hF hr₁) hr₁.hasCagladPaths_leftLimitProcess
  have hJ₂ : IsSemimartingale J₂ F P :=
    ((hX.isSemimartingale_quadraticVariation hF).isSemimartingale_stochasticIntegral hF
      (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess).const_mul (1 / 2)
  let C₀ : ℝ≥0 → Ω → ℝ := fun _ ω ↦ f (X 0 ω)
  have hC : IsSemimartingale C₀ F P := isSemimartingale_const_initial
    (hf.continuous.measurable.comp (hX.adapted 0))
  let V : ℝ≥0 → Ω → ℝ := (fun t ω ↦ f (X t ω)) - C₀ - J₁ - J₂
  let R : ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
    (f (X s ω) - f (leftLimitProcess X s ω) -
      deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
      deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)
  have hvR : HasFiniteVariationPaths R P :=
    hX.hasFiniteVariationPaths_contDiff_second_order_jump_remainders hF hf
  have he : Indistinguishable V R P := by
    filter_upwards [hX.ito_raw_bracket hF hf] with ω hω t
    have h := hω t
    change f (X t ω) - f (X 0 ω) = J₁ t ω + J₂ t ω + R t ω at h
    change f (X t ω) - f (X 0 ω) - J₁ t ω - J₂ t ω = R t ω
    linarith only [h]
  have hv : HasFiniteVariationPaths V P := HasFiniteVariationPaths.congr he.symm hvR
  have haV : Adapted F V := fun t ↦
    (((hf.continuous.measurable.comp (hX.adapted t)).sub (hC.adapted t)).sub
      (hJ₁.adapted t)).sub (hJ₂.adapted t)
  have hrV : HasCadlagPaths V P :=
    (((hX.hasCadlagPaths.continuous_comp hf.continuous).sub hC.hasCadlagPaths).sub
      hJ₁.hasCadlagPaths).sub hJ₂.hasCadlagPaths
  have hV := hv.isSemimartingale haV hF hrV
  apply (hC.add (hJ₁.add (hJ₂.add hV))).congr_of_adapted _
    (fun t ↦ hf.continuous.measurable.comp (hX.adapted t))
  exact ae_of_all _ (fun ω t ↦ by
    change f (X 0 ω) + (J₁ t ω + (J₂ t ω +
      (f (X t ω) - f (X 0 ω) - J₁ t ω - J₂ t ω))) = f (X t ω)
    ring)

end ProbabilityTheory
