/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.ContinuousCoordinates
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IsotropicIntegral
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousPaths
public import StochLean.Probability.Process.LocalMartingale.FiniteLinearCombination
public import StochLean.Probability.Process.LocalMartingale.Congr

/-! # Zero Hessian trace preserves continuous local martingales

This is the globally C2 coordinate-form core of Protter II.41. The common
clock need not be deterministic, strictly increasing, or integrable. The
arbitrary initial value of the composition is localized by the existing
Protter masks. The open-domain localization layer is a separate obligation.
-/

@[expose] public section

open MeasureTheory Filter Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem isContinuousLocalMartingale_comp_of_isotropic_trace_zero_on_paths
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (hf : ContDiff ℝ 2 f)
    (htrace : ∀ᵐ ω ∂P, ∀ t, ∑ i, coordinateSecondDeriv f i i (fun j ↦ X j t ω) = 0) :
    IsContinuousLocalMartingale (fun t ω ↦ f (fun i ↦ X i t ω)) F P := by
  let hS := fun i ↦ (hX i).isSemimartingale hF
  have haY : Adapted F (fun t ω ↦ f (fun i ↦ X i t ω)) := fun t ↦
    hf.continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun i ↦ (hS i).adapted t))
  have hinit := isContinuousLocalMartingale_const_initial (P := P) (haY 0)
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have := hι
    apply hinit.congr hF haY
    exact Eventually.of_forall (fun _ _ ↦ congrArg f (Subsingleton.elim _ _))
  | inr hι =>
    have := hι
    let k : ι := Classical.ofNonempty
    let hA := (hS k).isSemimartingale_continuousQuadraticVariation hF
    let ha₁ : ∀ i, Adapted F (fun t ω ↦ coordinateDeriv f i (fun j ↦ X j t ω)) :=
      fun i t ↦ (contDiff_coordinateDeriv hf i).continuous.measurable.comp
        (@measurable_pi_lambda _ _ _ (F t) _ _ (fun j ↦ (hS j).adapted t))
    let hr₁ := fun i ↦ (HasCadlagPaths.pi (fun j ↦ (hS j).hasCadlagPaths)).continuous_comp
      (contDiff_coordinateDeriv hf i).continuous
    let ha₂ : ∀ i j, Adapted F
        (fun t ω ↦ coordinateSecondDeriv f i j (fun l ↦ X l t ω)) :=
      fun i j t ↦ (continuous_coordinateSecondDeriv hf i j).measurable.comp
        (@measurable_pi_lambda _ _ _ (F t) _ _ (fun l ↦ (hS l).adapted t))
    let hr₂ := fun i j ↦ (HasCadlagPaths.pi (fun l ↦ (hS l).hasCadlagPaths)).continuous_comp
      (continuous_coordinateSecondDeriv hf i j)
    let haL := fun i j ↦ (ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j)
    let hrL := fun i j ↦ (hr₂ i j).hasCagladPaths_leftLimitProcess
    have hz : Indistinguishable (fun t ω ↦ ∑ i, leftLimitProcess
        (fun s v ↦ coordinateSecondDeriv f i i (fun j ↦ X j s v)) t ω) 0 P := by
      filter_upwards [ae_all_iff.2 (fun i ↦ (hX i).2), htrace] with ω hω htω t
      change (∑ i, leftLimitProcess
        (fun s v ↦ coordinateSecondDeriv f i i (fun j ↦ X j s v)) t ω) = 0
      by_cases ht : t = 0
      · subst t
        simp only [leftLimitProcess_zero, Pi.zero_apply, sum_const_zero]
      · have hp : 0 < t := lt_of_le_of_ne zero_le (Ne.symm ht)
        simp_rw [leftLimitProcess_continuous_comp_coordinates_of_pos
          (fun i ↦ (hω i).isCadlagPath) (continuous_coordinateSecondDeriv hf _ _) hp,
          fun i ↦ (hω i).leftLimitProcess_eq (ne_of_gt hp)]
        exact htω t
    have hbr := continuousQuadraticCovariation_integral_sum_eq_zero_of_trace_eq_zero
      hS hA hF (fun i ↦ ((hS i).continuousQuadraticCovariation_self hF).trans
        ((hd i).trans (hd k).symm)) ho haL hrL hz
    let G := fun i ↦ (hS i).stochasticIntegral hF
      ((ha₁ i).leftLimitProcess_of_usual hF (hr₁ i))
      (hr₁ i).hasCagladPaths_leftLimitProcess
    have hG : IsContinuousLocalMartingale (fun t ω ↦ ∑ i, G i t ω) F P := by
      have hsum := isContinuousLocalMartingale_finset_sum univ hF (fun i _ ↦
        (hX i).isContinuousLocalMartingale_stochasticIntegral hF
          ((ha₁ i).leftLimitProcess_of_usual hF (hr₁ i))
          (hr₁ i).hasCagladPaths_leftLimitProcess)
      convert hsum using 1
      funext t ω
      simp only [G, Finset.sum_apply]
    apply (hG.add hinit hF).congr hF haY
    filter_upwards [ito_continuous_finiteCoordinates hS hF (fun i ↦ (hX i).2) hf, hbr]
      with ω hi hb t
    have hi' := hi t
    rw [hb t] at hi'
    change (∑ i, G i t ω) + f (fun i ↦ X i 0 ω) = f (fun i ↦ X i t ω)
    change f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) = (∑ i, G i t ω) +
      (1 / 2 : ℝ) * (0 : ℝ≥0 → Ω → ℝ) t ω at hi'
    simp only [Pi.zero_apply, mul_zero, add_zero] at hi'
    linarith only [hi']

end ProbabilityTheory
