/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.VectorContinuousBracket

/-! # Ito's formula for continuous finite-coordinate processes

The jump correction vanishes on the common event of coordinate continuity.
The integral is still the original source integral, with left-limit integrands
and all ordered Hessian pairs of the canonical continuous mixed bracket.
-/

@[expose] public section

open MeasureTheory Set Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem ito_continuous_finiteCoordinates
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    (hc : ∀ i, HasContinuousPaths (X i) P) (hf : ContDiff ℝ 2 f) :
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
            (hr₂ i j).hasCagladPaths_leftLimitProcess t ω)) P := by
  dsimp only
  filter_upwards [ito_finiteCoordinates_continuous_bracket hX hF hf, ae_all_iff.2 hc]
    with ω hi hω t
  have hj (s : Ioc 0 t) : f (fun i ↦ X i s ω) -
      f (fun i ↦ leftLimitProcess (X i) s ω) -
      ∑ i, coordinateDeriv f i (fun j ↦ leftLimitProcess (X j) s ω) *
        jumpProcess (X i) s ω = 0 := by
    have hl (i : ι) := (hω i).leftLimitProcess_eq (ne_of_gt s.2.1)
    have hz (i : ι) := (hω i).jumpProcess_eq_zero (ne_of_gt s.2.1)
    simp only [hl, hz, mul_zero, sum_const_zero, sub_self]
  simpa only [hj, tsum_zero, add_zero] using hi t

end ProbabilityTheory
