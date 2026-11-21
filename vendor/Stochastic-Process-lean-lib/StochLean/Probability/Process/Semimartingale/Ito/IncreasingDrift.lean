/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.TraceZero
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Increasing

/-! # The actual increasing Ito drift for nonnegative Hessian trace

The witness is one half of the existing common-clock integral of the diagonal
Hessian sum. It is continuous, adapted, increasing and zero initially. After
subtracting it, the composition is a canonical continuous local martingale.
No moment or deterministic-clock hypothesis is imposed.
-/

@[expose] public section

open MeasureTheory Filter Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem exists_isotropic_ito_increasing_drift
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
    (htrace : ∀ᵐ ω ∂P, ∀ t, 0 ≤ ∑ i, coordinateSecondDeriv f i i (fun j ↦ X j t ω)) :
    ∃ D : ℝ≥0 → Ω → ℝ, Adapted F D ∧ HasContinuousPaths D P ∧ HasMonotonePaths D P ∧
      D 0 =ᵐ[P] 0 ∧
      IsContinuousLocalMartingale (fun t ω ↦ f (fun i ↦ X i t ω) - D t ω) F P := by
  let hS := fun i ↦ (hX i).isSemimartingale hF
  have haY : Adapted F (fun t ω ↦ f (fun i ↦ X i t ω)) := fun t ↦
    hf.continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun i ↦ (hS i).adapted t))
  have hinit := isContinuousLocalMartingale_const_initial (P := P) (haY 0)
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have := hι
    refine ⟨0, fun _ ↦ measurable_const, Eventually.of_forall (fun _ ↦ continuous_const),
      Eventually.of_forall (fun _ ↦ monotone_const), Eventually.of_forall (fun _ ↦ rfl), ?_⟩
    apply hinit.congr hF (haY.sub (fun _ ↦ measurable_const))
    filter_upwards with ω t
    change f (fun i ↦ X i 0 ω) = f (fun i ↦ X i t ω) - 0
    rw [sub_zero]
    exact congrArg f (Subsingleton.elim _ _)
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
    let haT := fun t ↦ Finset.measurable_sum univ (fun i _ ↦ haL i i t)
    let hrT := HasCagladPaths.finset_sum univ (fun i _ ↦ hrL i i)
    let I := hA.stochasticIntegral hF haT hrT
    let D := fun t ω ↦ (1 / 2 : ℝ) * I t ω
    have haD : Adapted F D := fun t ↦
      measurable_const.mul (hA.adapted_stochasticIntegral hF haT hrT t)
    have hcD : HasContinuousPaths D P := by
      filter_upwards [hA.hasContinuousPaths_stochasticIntegral hF haT hrT
        ((hS k).hasContinuousPaths_continuousQuadraticVariation hF)] with ω hω
      exact continuous_const.mul hω
    have hpos : ∀ᵐ ω ∂P, ∀ t, 0 ≤ ∑ i, leftLimitProcess
        (fun s v ↦ coordinateSecondDeriv f i i (fun j ↦ X j s v)) t ω := by
      filter_upwards [ae_all_iff.2 (fun i ↦ (hX i).2), htrace] with ω hω htω t
      by_cases ht : t = 0
      · subst t
        simp only [leftLimitProcess_zero, Pi.zero_apply, sum_const_zero, le_refl]
      · have hp : 0 < t := lt_of_le_of_ne zero_le (Ne.symm ht)
        simp_rw [leftLimitProcess_continuous_comp_coordinates_of_pos
          (fun i ↦ (hω i).isCadlagPath) (continuous_coordinateSecondDeriv hf _ _) hp,
          fun i ↦ (hω i).leftLimitProcess_eq (ne_of_gt hp)]
        exact htω t
    have hmD : HasMonotonePaths D P := by
      filter_upwards [hA.hasMonotonePaths_stochasticIntegral hF
        (Eventually.of_forall ((hS k).monotone_continuousQuadraticVariation hF)) haT hrT hpos]
        with ω hω s t hst
      exact mul_le_mul_of_nonneg_left (hω hst) (by norm_num)
    have hD0 : D 0 =ᵐ[P] 0 := by
      filter_upwards [hA.stochasticIntegral_zero_ae hF haT hrT] with ω hω
      change (1 / 2 : ℝ) * I 0 ω = 0
      simp only [I, hω, IsSemimartingale.continuousQuadraticVariation_zero, mul_zero]
    refine ⟨D, haD, hcD, hmD, hD0, ?_⟩
    have hbr := continuousQuadraticCovariation_integral_sum_of_isotropic hS hA hF
      (fun i ↦ ((hS i).continuousQuadraticCovariation_self hF).trans
        ((hd i).trans (hd k).symm)) ho haL hrL
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
    apply (hG.add hinit hF).congr hF (haY.sub haD)
    filter_upwards [ito_continuous_finiteCoordinates hS hF (fun i ↦ (hX i).2) hf, hbr]
      with ω hi hb t
    have hi' := hi t
    rw [hb t] at hi'
    change f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) =
      (∑ i, G i t ω) + (1 / 2 : ℝ) * I t ω at hi'
    change (∑ i, G i t ω) + f (fun i ↦ X i 0 ω) =
      f (fun i ↦ X i t ω) - (1 / 2 : ℝ) * I t ω
    linarith only [hi']

end ProbabilityTheory
