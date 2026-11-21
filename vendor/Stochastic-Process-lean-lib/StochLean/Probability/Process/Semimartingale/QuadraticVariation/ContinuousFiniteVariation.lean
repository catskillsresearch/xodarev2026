/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationLocality
public import StochLean.Analysis.PathVariation.C1ChangeOfVariables

/-! # The raw bracket on continuous finite-variation paths

The assertion is local to sample paths: the finite-variation event need not
have full measure. The initial square remains, even for a nonzero constant.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticVariation_on_continuous_finiteVariation_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, IsContinuousPath (X · ω) →
      LocallyBoundedVariationOn (X · ω) univ →
      ∀ t : ℝ≥0, hX.quadraticVariation hF t ω = (X 0 ω) ^ 2 := by
  let ha := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hr := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  filter_upwards [hX.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation hF ha hr]
    with ω hI hc hv
  obtain ⟨hωr, he⟩ := hI hv
  intro t
  have hi : pathStieltjesIncrementIntegral (X · ω) hv hωr.1
      (leftLimitProcess X · ω) 0 t =
      pathStieltjesIncrementIntegral (X · ω) hv hωr.1 (X · ω) 0 t := by
    apply pathStieltjesIncrementIntegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hc.leftLimitProcess_eq (ne_of_gt hs.1)
  have hs := pathStieltjesIntegral_self_of_continuous
    (hv := hv) (hr := hωr.1) (T := t) hc.continuousOn
  change X 0 ω * X 0 ω + pathStieltjesIncrementIntegral (X · ω) hv hωr.1
    (X · ω) 0 t = ((X t ω) ^ 2 + (X 0 ω) ^ 2) / 2 at hs
  change (X t ω) ^ 2 - 2 * hX.stochasticIntegral hF ha hr t ω = (X 0 ω) ^ 2
  rw [he t]
  simp only [pathStieltjesIntegral, leftLimitProcess_zero, Pi.zero_apply, zero_mul, zero_add, hi]
  linarith

theorem IsSemimartingale.quadraticVariation_of_continuous_finiteVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.quadraticVariation hF) (fun _ ω ↦ (X 0 ω) ^ 2) P := by
  filter_upwards [hX.quadraticVariation_on_continuous_finiteVariation_paths hF, hc, hv]
    with ω h hcω hvω
  exact h hcω hvω

end ProbabilityTheory
