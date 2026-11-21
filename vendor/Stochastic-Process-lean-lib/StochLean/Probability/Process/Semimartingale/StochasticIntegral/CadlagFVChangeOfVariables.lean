/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CadlagChangeOfVariables
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationLocality
public import StochLean.Probability.Process.Measurability.LeftLimit

/-! # The cadlag FV C1 formula for the existing Chapter II stochastic integral

The source left limit is zero at time zero, so `f'(X_-) . X` has initial
value `f'(0) X_0`. The increment formula subtracts exactly this initial term.
Only positive-time jumps occur in the actual absolutely summable series.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.contDiff_change_of_variables_on_finiteVariation_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 1 f) :
    let ha : Adapted F (fun t ω ↦ deriv f (leftLimitProcess X t ω)) := fun t ↦
      hf.continuous_deriv_one.measurable.comp
        (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths t)
    let hr := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess.continuous_comp
      hf.continuous_deriv_one
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (X · ω) univ → ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ |f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω|) ∧
      f (X t ω) - f (X 0 ω) = hX.stochasticIntegral hF ha hr t ω - deriv f 0 * X 0 ω +
        ∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω) := by
  dsimp only
  let ha : Adapted F (fun t ω ↦ deriv f (leftLimitProcess X t ω)) := fun t ↦
    hf.continuous_deriv_one.measurable.comp
      (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths t)
  let hr := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess.continuous_comp
    hf.continuous_deriv_one
  filter_upwards [hX.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation hF ha hr]
    with ω hI hv
  obtain ⟨hc, he⟩ := hI hv
  intro t
  have hj (s : Ioc 0 t) : leftLimitProcess X s ω = Function.leftLim (X · ω) s := by
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hs := summable_abs_contDiff_jump_remainders hv hc hf t
  have hvf := pathStieltjesIncrementIntegral_contDiff_cadlag hv hc hf t
  have hi : hX.stochasticIntegral hF ha hr t ω = deriv f 0 * X 0 ω +
      pathStieltjesIncrementIntegral (X · ω) hv hc.1
        (fun s ↦ deriv f (Function.leftLim (X · ω) s)) 0 t := by
    rw [he t]
    simp only [pathStieltjesIntegral, leftLimitProcess_zero, Pi.zero_apply]
    congr 1
    apply pathStieltjesIncrementIntegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [leftLimitProcess, if_neg (ne_of_gt hs.1)]
  refine ⟨?_, ?_⟩
  · simpa only [jumpProcess, Pi.sub_apply, hj] using hs
  · rw [hi]
    simpa only [jumpProcess, Pi.sub_apply, hj, add_sub_cancel_left] using hvf

theorem IsSemimartingale.contDiff_change_of_variables_of_finiteVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P)
    (hf : ContDiff ℝ 1 f) :
    let ha : Adapted F (fun t ω ↦ deriv f (leftLimitProcess X t ω)) := fun t ↦
      hf.continuous_deriv_one.measurable.comp
        (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths t)
    let hr := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess.continuous_comp
      hf.continuous_deriv_one
    Indistinguishable (fun t ω ↦ f (X t ω) - f (X 0 ω))
      (fun t ω ↦ hX.stochasticIntegral hF ha hr t ω - deriv f 0 * X 0 ω +
        ∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω)) P := by
  filter_upwards [hX.contDiff_change_of_variables_on_finiteVariation_paths hF hf, hv]
    with ω he hvω t
  exact (he hvω t).2

end ProbabilityTheory
