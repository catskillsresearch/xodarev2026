/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IncrementBound
public import StochLean.Analysis.PathVariation.StieltjesKunitaWatanabe

/-! # Kunita--Watanabe for the canonical semimartingale covariation

One full-measure event supplies the actual Stieltjes realizations of both
square brackets and the canonical variation measure of the mixed bracket.
On that event the inequality holds for every pair of measurable weights,
with no finite-energy assumption. No second stochastic bracket, arbitrary
process fallback, or assumed density estimate is introduced.

These are increment Stieltjes measures, with zero mass at time zero. The
already proved raw initial values are unchanged and remain separate terms.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.eVariationOn_quadraticCovariation_le
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t,
      eVariationOn (fun u ↦ hX.quadraticCovariation hY hF u ω) (Icc s t) ≤
        ENNReal.ofReal (Real.sqrt (hX.quadraticVariation hF t ω - hX.quadraticVariation hF s ω) *
          Real.sqrt (hY.quadraticVariation hF t ω - hY.quadraticVariation hF s ω)) := by
  filter_upwards [hX.abs_quadraticCovariation_increment_le hY hF,
    hX.hasMonotonePaths_quadraticVariation hF, hY.hasMonotonePaths_quadraticVariation hF]
    with ω hinc hx hy s t
  exact eVariationOn_le_of_covariation_increment_bound hx hy hinc s t

theorem IsSemimartingale.exists_kunitaWatanabe_stieltjes
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P,
      ∃ (hv : LocallyBoundedVariationOn (fun t ↦ hX.quadraticCovariation hY hF t ω) univ)
        (hr : ∀ t, ContinuousWithinAt (fun u ↦ hX.quadraticCovariation hY hF u ω) (Ici t) t)
        (B C : StieltjesFunction ℝ≥0),
        (∀ t, B t = hX.quadraticVariation hF t ω) ∧
        (∀ t, C t = hY.quadraticVariation hF t ω) ∧
        (∀ (f g : ℝ≥0 → ℝ≥0∞), Measurable f → Measurable g →
          (∫⁻ t, f t * g t ∂(totalVariationStieltjes _ hv hr).measure) ≤
            (∫⁻ t, (f t) ^ 2 ∂B.measure) ^ (1 / 2 : ℝ) *
              (∫⁻ t, (g t) ^ 2 ∂C.measure) ^ (1 / 2 : ℝ)) ∧
        (totalVariationStieltjes _ hv hr).measure ≪ B.measure ∧
        (totalVariationStieltjes _ hv hr).measure ≪ C.measure := by
  filter_upwards [hX.hasFiniteVariationPaths_quadraticCovariation hY hF,
    hX.hasCadlagPaths_quadraticCovariation hY hF,
    hX.hasMonotonePaths_quadraticVariation hF, hX.hasCadlagPaths_quadraticVariation hF,
    hY.hasMonotonePaths_quadraticVariation hF, hY.hasCadlagPaths_quadraticVariation hF,
    hX.abs_quadraticCovariation_increment_le hY hF] with ω hv hr hmX hrX hmY hrY hinc
  let B : StieltjesFunction ℝ≥0 := ⟨fun t ↦ hX.quadraticVariation hF t ω, hmX, hrX.1⟩
  let C : StieltjesFunction ℝ≥0 := ⟨fun t ↦ hY.quadraticVariation hF t ω, hmY, hrY.1⟩
  refine ⟨hv, hr.1, B, C, fun _ ↦ rfl, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · exact fun _ _ hf hg ↦ stieltjes_lintegral_mul_le_of_increment_bound hv hr.1 B C hinc hf hg
  · exact totalVariationStieltjes_absolutelyContinuous_left_of_increment_bound hv hr.1 B C hinc
  · exact totalVariationStieltjes_absolutelyContinuous_right_of_increment_bound hv hr.1 B C hinc

end ProbabilityTheory
