/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.VectorContinuousBracket
public import StochLean.Probability.Process.Semimartingale.Complex.GradientIntegral
public import StochLean.Probability.Process.Semimartingale.Complex.HessianIntegral
public import StochLean.Probability.Process.Semimartingale.Complex.JumpSummability

/-! # Real linear components of the complex cadlag Ito formula

The proof applies the real two-dimensional theorem and identifies every
coordinate integral. Commutation with the actual jump series uses its
proved absolute convergence, not the default value of a divergent tsum.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsComplexSemimartingale.ito_continuous_bracket_component
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ} {f : ℂ → ℂ}
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P)
    (hf : Differentiable ℂ f) (L : ℂ →L[ℝ] ℝ) :
    let ha₁ : Adapted F (fun t ω ↦ deriv f (Z t ω)) :=
      fun t ↦ hf.deriv.continuous.measurable.comp (hZ.adapted t)
    let hr₁ := hZ.hasCadlagPaths.continuous_comp hf.deriv.continuous
    let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (Z t ω)) :=
      fun t ↦ hf.deriv.deriv.continuous.measurable.comp (hZ.adapted t)
    let hr₂ := hZ.hasCadlagPaths.continuous_comp hf.deriv.deriv.continuous
    Indistinguishable (fun t ω ↦ L (f (Z t ω) - f (Z 0 ω)))
      (fun t ω ↦ L (hZ.stochasticIntegral hF
          (Adapted.complexLeftLimitProcess_of_usual ha₁ hF hr₁)
          hr₁.hasCagladPaths_complexLeftLimitProcess t ω +
        (1 / 2 : ℝ) •
          (hZ.isComplexSemimartingale_continuousQuadraticVariation hF).stochasticIntegral
            hF (Adapted.complexLeftLimitProcess_of_usual ha₂ hF hr₂)
            hr₂.hasCagladPaths_complexLeftLimitProcess t ω +
        ∑' s : Ioc 0 t, (f (Z s ω) - f (complexLeftLimitProcess Z s ω) -
          deriv f (complexLeftLimitProcess Z s ω) * complexJumpProcess Z s ω))) P := by
  dsimp only
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
  let g : (Fin 2 → ℝ) → ℝ := fun x ↦ L (f (complexCoordinates x))
  have hg : ContDiff ℝ 2 g := contDiff_complex_coordinate_component hf L
  let ha₁ : Adapted F (fun t ω ↦ deriv f (Z t ω)) :=
    fun t ↦ hf.deriv.continuous.measurable.comp (hZ.adapted t)
  let hr₁ := hZ.hasCadlagPaths.continuous_comp hf.deriv.continuous
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (Z t ω)) :=
    fun t ↦ hf.deriv.deriv.continuous.measurable.comp (hZ.adapted t)
  let hr₂ := hZ.hasCadlagPaths.continuous_comp hf.deriv.deriv.continuous
  let haG : ∀ i, Adapted F (fun t ω ↦ coordinateDeriv g i (fun j ↦ X j t ω)) :=
    fun i t ↦ (contDiff_coordinateDeriv hg i).continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun j ↦ (hX j).adapted t))
  let hrG := fun i ↦ (HasCadlagPaths.pi (fun j ↦ (hX j).hasCadlagPaths)).continuous_comp
    (contDiff_coordinateDeriv hg i).continuous
  let haH : ∀ i j, Adapted F
      (fun t ω ↦ coordinateSecondDeriv g i j (fun k ↦ X k t ω)) :=
    fun i j t ↦ (continuous_coordinateSecondDeriv hg i j).measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun k ↦ (hX k).adapted t))
  let hrH := fun i j ↦ (HasCadlagPaths.pi (fun k ↦ (hX k).hasCadlagPaths)).continuous_comp
    (continuous_coordinateSecondDeriv hg i j)
  have hg₀ (t : ℝ≥0) (ω : Ω) : coordinateDeriv g 0 (fun i ↦ X i t ω) =
      L (deriv f (Z t ω)) := by
    simp only [g, complex_component_coordinate_gradient hf, he, Matrix.cons_val_zero]
  have hg₁ (t : ℝ≥0) (ω : Ω) : coordinateDeriv g 1 (fun i ↦ X i t ω) =
      L (Complex.I * deriv f (Z t ω)) := by
    simp only [g, complex_component_coordinate_gradient hf, he, Matrix.cons_val_one,
      Matrix.cons_val_zero, mul_comm]
  have hgrad := (hX 0).stochasticIntegral_complex_left_gradient (hX 1) hF ha₁ hr₁ L
    (haG 0) (hrG 0) (haG 1) (hrG 1) hg₀ hg₁
  have hh (i j : Fin 2) (t : ℝ≥0) (ω : Ω) :
      coordinateSecondDeriv g i j (fun k ↦ X k t ω) =
        ![![L (deriv (deriv f) (Z t ω)), L (Complex.I * deriv (deriv f) (Z t ω))],
          ![L (Complex.I * deriv (deriv f) (Z t ω)), -L (deriv (deriv f) (Z t ω))]] i j := by
    simp only [g, complex_component_coordinate_hessian hf, he, mul_comm]
  have hhess := stochasticIntegral_complex_left_hessian hX hF ha₂ hr₂ L haH hrH hh
  filter_upwards [ito_finiteCoordinates_continuous_bracket hX hF hg, hgrad, hhess,
    hZ.summable_norm_differentiable_jump_remainders hF hf] with ω hi hgradω hhessω hs t
  have hseries : (∑' s : Ioc 0 t,
      (g (fun i ↦ X i s ω) - g (fun i ↦ leftLimitProcess (X i) s ω) -
        ∑ i, coordinateDeriv g i (fun j ↦ leftLimitProcess (X j) s ω) *
          jumpProcess (X i) s ω)) =
      L (∑' s : Ioc 0 t, (f (Z s ω) - f (complexLeftLimitProcess Z s ω) -
        deriv f (complexLeftLimitProcess Z s ω) * complexJumpProcess Z s ω)) := by
    rw [L.map_tsum (hs t).of_norm]
    apply tsum_congr
    intro s
    rw [← fderiv_apply_eq_sum_coordinateDeriv]
    have hj : (fun i ↦ jumpProcess (X i) s ω) =
        (fun i ↦ X i s ω) - (fun i ↦ leftLimitProcess (X i) s ω) := rfl
    rw [hj]
    simpa only [g, he, hl, complexJumpProcess, Pi.sub_apply] using
      complex_coordinate_first_order_remainder hf L
        (fun i ↦ leftLimitProcess (X i) s ω) (fun i ↦ X i s ω)
  have hform := hi t
  rw [hseries, hhessω t, Fin.sum_univ_two] at hform
  have hgrad' := hgradω t
  simp only [Pi.add_apply] at hgrad'
  rw [hgrad'] at hform
  simpa only [g, he, map_sub, map_add, map_smul, smul_eq_mul, X, complexProcess,
    stochasticIntegral, continuousQuadraticVariation,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hform

end ProbabilityTheory
