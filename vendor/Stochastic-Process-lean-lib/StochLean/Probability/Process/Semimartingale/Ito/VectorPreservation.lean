/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.VectorRawBracket
public import StochLean.Probability.Process.Semimartingale.Ito.VectorJumpVariation
public import StochLean.Probability.Process.Semimartingale.FiniteSum
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation

/-! # C2 functions of finitely many cadlag semimartingales are semimartingales

The adapted cadlag residual is identified with the actual finite-variation
jump series. Nonlinear closure is a conclusion, not an input assumption.
-/

@[expose] public section

open MeasureTheory Set Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem isSemimartingale_contDiff_comp_finiteCoordinates
    {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    IsSemimartingale (fun t ω ↦ f (fun i ↦ X i t ω)) F P := by
  classical
  let ha₁ : ∀ i, Adapted F (fun t ω ↦ coordinateDeriv f i (fun j ↦ X j t ω)) :=
    fun i t ↦ (contDiff_coordinateDeriv hf i).continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun j ↦ (hX j).adapted t))
  let hr₁ := fun i ↦ (HasCadlagPaths.pi (fun j ↦ (hX j).hasCadlagPaths)).continuous_comp
    (contDiff_coordinateDeriv hf i).continuous
  let ha₂ : ∀ i j, Adapted F
      (fun t ω ↦ coordinateSecondDeriv f i j (fun k ↦ X k t ω)) :=
    fun i j t ↦ (continuous_coordinateSecondDeriv hf i j).measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun k ↦ (hX k).adapted t))
  let hr₂ := fun i j ↦ (HasCadlagPaths.pi (fun k ↦ (hX k).hasCadlagPaths)).continuous_comp
    (continuous_coordinateSecondDeriv hf i j)
  let J₁ : ℝ≥0 → Ω → ℝ := ∑ i, (hX i).stochasticIntegral hF
    ((ha₁ i).leftLimitProcess_of_usual hF (hr₁ i)) (hr₁ i).hasCagladPaths_leftLimitProcess
  let J₂ : ℝ≥0 → Ω → ℝ := (1 / 2 : ℝ) • ∑ i, ∑ j,
    ((hX i).isSemimartingale_quadraticCovariation (hX j) hF).stochasticIntegral hF
      ((ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j))
      (hr₂ i j).hasCagladPaths_leftLimitProcess
  have hJ₁ : IsSemimartingale J₁ F P := IsSemimartingale.finset_sum univ (fun i _ ↦
    (hX i).isSemimartingale_stochasticIntegral hF
      ((ha₁ i).leftLimitProcess_of_usual hF (hr₁ i)) (hr₁ i).hasCagladPaths_leftLimitProcess)
  have hJ₂ : IsSemimartingale J₂ F P :=
    (IsSemimartingale.finset_sum univ (fun i _ ↦
      IsSemimartingale.finset_sum univ (fun j _ ↦
        ((hX i).isSemimartingale_quadraticCovariation (hX j) hF).isSemimartingale_stochasticIntegral
          hF
            ((ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j))
            (hr₂ i j).hasCagladPaths_leftLimitProcess))).const_mul (1 / 2)
  have ha : Adapted F (fun t ω ↦ f (fun i ↦ X i t ω)) := fun t ↦
    hf.continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun i ↦ (hX i).adapted t))
  have hr := (HasCadlagPaths.pi (fun i ↦ (hX i).hasCadlagPaths)).continuous_comp hf.continuous
  let C₀ : ℝ≥0 → Ω → ℝ := fun _ ω ↦ f (fun i ↦ X i 0 ω)
  have hC : IsSemimartingale C₀ F P := isSemimartingale_const_initial (ha 0)
  let V : ℝ≥0 → Ω → ℝ := (fun t ω ↦ f (fun i ↦ X i t ω)) - C₀ - J₁ - J₂
  let R : ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
    frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω) (fun i ↦ X i s ω)
  have hvR : HasFiniteVariationPaths R P :=
    hasFiniteVariationPaths_frechet_second_order_jump_remainders hX hF hf
  have he : Indistinguishable V R P := by
    filter_upwards [ito_finiteCoordinates_raw_bracket hX hF hf] with ω hω t
    have h : f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) =
        J₁ t ω + J₂ t ω + R t ω := by
      simpa only [J₁, J₂, R, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hω t
    change f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) - J₁ t ω - J₂ t ω = R t ω
    linarith only [h]
  have hv : HasFiniteVariationPaths V P := HasFiniteVariationPaths.congr he.symm hvR
  have haV : Adapted F V := fun t ↦
    (((ha t).sub (hC.adapted t)).sub (hJ₁.adapted t)).sub (hJ₂.adapted t)
  have hrV : HasCadlagPaths V P :=
    ((hr.sub hC.hasCadlagPaths).sub hJ₁.hasCadlagPaths).sub hJ₂.hasCadlagPaths
  have hV := hv.isSemimartingale haV hF hrV
  apply (hC.add (hJ₁.add (hJ₂.add hV))).congr_of_adapted _ ha
  exact ae_of_all _ (fun ω t ↦ by
    change f (fun i ↦ X i 0 ω) + (J₁ t ω + (J₂ t ω +
      (f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) - J₁ t ω - J₂ t ω))) = _
    ring)

end ProbabilityTheory
