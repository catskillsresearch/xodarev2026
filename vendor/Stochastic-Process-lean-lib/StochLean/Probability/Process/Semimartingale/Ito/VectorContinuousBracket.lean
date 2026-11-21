/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.VectorRawBracket
public import StochLean.Probability.Process.Semimartingale.Ito.VectorPreservation
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegralDecomposition
public import StochLean.Probability.Process.Path.LeftLimitFiniteComposition
public import StochLean.ForMathlib.Analysis.FiniteCoordinateTaylorSeries

/-! # Protter II.33: the finite-dimensional cadlag Ito formula

The formula uses all ordered coordinate pairs of the canonical continuous
mixed bracket and the actual first-order jump series. The proof converts
the raw identity using proved integral decomposition and absolute summability.
-/

@[expose] public section

open MeasureTheory Set Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem ito_finiteCoordinates_continuous_bracket
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
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
    Indistinguishable (fun t ω ↦ f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω))
      (fun t ω ↦ (∑ i, (hX i).stochasticIntegral hF
          ((ha₁ i).leftLimitProcess_of_usual hF (hr₁ i))
          (hr₁ i).hasCagladPaths_leftLimitProcess t ω) +
        (1 / 2 : ℝ) * (∑ i, ∑ j,
          ((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF).stochasticIntegral
            hF ((ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j))
            (hr₂ i j).hasCagladPaths_leftLimitProcess t ω) +
        ∑' s : Ioc 0 t, (f (fun i ↦ X i s ω) -
          f (fun i ↦ leftLimitProcess (X i) s ω) -
          ∑ i, coordinateDeriv f i (fun j ↦ leftLimitProcess (X j) s ω) *
            jumpProcess (X i) s ω)) P := by
  dsimp only
  let ha₂ : ∀ i j, Adapted F
      (fun t ω ↦ coordinateSecondDeriv f i j (fun k ↦ X k t ω)) :=
    fun i j t ↦ (continuous_coordinateSecondDeriv hf i j).measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun k ↦ (hX k).adapted t))
  let hr₂ := fun i j ↦ (HasCadlagPaths.pi (fun k ↦ (hX k).hasCadlagPaths)).continuous_comp
    (continuous_coordinateSecondDeriv hf i j)
  have hD := ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun j ↦
    (hX i).stochasticIntegral_quadraticCovariation_continuous_jump_decomposition (hX j) hF
      ((ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j))
      (hr₂ i j).hasCagladPaths_leftLimitProcess))
  have hS := ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun j ↦
    (hX i).summable_abs_caglad_weighted_mixed_jumps (hX j) hF
      (hr₂ i j).hasCagladPaths_leftLimitProcess))
  have hpaths := ae_all_iff.mpr (fun i ↦ (hX i).hasCadlagPaths)
  filter_upwards [ito_finiteCoordinates_raw_bracket hX hF hf, hD, hS, hpaths,
    summable_abs_frechet_semimartingale_jump_remainders hX hF hf]
      with ω hi hd hs hx hR t
  have hleft (i j : ι) (s : Ioc 0 t) :
      leftLimitProcess (fun u v ↦ coordinateSecondDeriv f i j (fun k ↦ X k u v)) s ω =
        coordinateSecondDeriv f i j (fun k ↦ leftLimitProcess (X k) s ω) :=
    leftLimitProcess_continuous_comp_coordinates_of_pos hx
      (continuous_coordinateSecondDeriv hf i j) s.2.1
  let W : ι → ι → Ioc 0 t → ℝ := fun i j s ↦
    coordinateSecondDeriv f i j (fun k ↦ leftLimitProcess (X k) s ω) *
      jumpProcess (X i) s ω * jumpProcess (X j) s ω
  have hW (i j : ι) : Summable (W i j) := by
    simpa only [W, hleft, mul_assoc] using (hs i j t).of_abs
  have hj (s : Ioc 0 t) : (fun i ↦ X i s ω) - (fun i ↦ leftLimitProcess (X i) s ω) =
      fun i ↦ jumpProcess (X i) s ω := rfl
  have hseries := tsum_frechetSecondOrderRemainder_eq_coordinate_correction f
    (fun (s : Ioc 0 t) i ↦ leftLimitProcess (X i) s ω) (fun s i ↦ X i s ω)
    (by simpa only [hj] using (hR t).1.of_abs) (fun i j ↦ hW i j)
  simp only [fderiv_apply_eq_sum_coordinateDeriv, Pi.sub_apply] at hseries
  let JC : ι → ι → ℝ := fun i j ↦
    ((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF).stochasticIntegral hF
      ((ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j))
      (hr₂ i j).hasCagladPaths_leftLimitProcess t ω
  have hd' (i j : ι) :
      ((hX i).isSemimartingale_quadraticCovariation (hX j) hF).stochasticIntegral hF
        ((ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j))
        (hr₂ i j).hasCagladPaths_leftLimitProcess t ω = JC i j + ∑' s, W i j s := by
    simpa only [JC, W, leftLimitProcess_zero, Pi.zero_apply, zero_mul, zero_add,
      hleft, mul_assoc] using hd i j t
  have hi' := hi t
  rw [hseries] at hi'
  simp only [hd', sum_add_distrib] at hi'
  change _ = _ + (1 / 2 : ℝ) * _ + _ at hi'
  dsimp only [W, JC] at hi'
  change _ = _ + (1 / 2 : ℝ) * _ + _
  dsimp only [jumpProcess] at hi' ⊢
  simp only [Pi.sub_apply] at hi' ⊢
  linarith only [hi']

end ProbabilityTheory
