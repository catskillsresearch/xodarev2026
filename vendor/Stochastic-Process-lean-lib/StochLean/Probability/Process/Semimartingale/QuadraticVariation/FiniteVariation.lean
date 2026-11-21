/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesSelfJump
public import StochLean.Analysis.PathVariation.StieltjesJumpIntegral
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPart
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationLocality

/-! # Protter II.26: raw quadratic variation on finite-variation paths

The actual jump series is obtained from Stieltjes component integrals. The
path-local assertion does not require the FV event to have full measure.
The initial square and all positive-time endpoint jumps are retained.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticVariation_on_finiteVariation_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (X · ω) univ → ∀ t : ℝ≥0,
      hX.quadraticVariation hF t ω = (X 0 ω) ^ 2 +
        ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2 := by
  let ha := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hr := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  filter_upwards [hX.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation hF ha hr]
    with ω hI hv
  obtain ⟨hc, he⟩ := hI hv
  intro t
  have hi : pathStieltjesIntegral (X · ω) hv hc.1 (leftLimitProcess X · ω) t =
      pathStieltjesIncrementIntegral (X · ω) hv hc.1 (Function.leftLim (X · ω)) 0 t := by
    simp only [pathStieltjesIntegral, leftLimitProcess_zero, Pi.zero_apply, zero_mul, zero_add]
    apply pathStieltjesIncrementIntegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [leftLimitProcess, if_neg (ne_of_gt hs.1)]
  change (X t ω) ^ 2 - 2 * hX.stochasticIntegral hF ha hr t ω = _
  rw [he t, hi, square_sub_twice_leftIntegral_eq_jumpIntegral hv hc t,
    pathStieltjesIncrementIntegral_jump_eq_tsum hv hc.1 t]
  congr 1
  apply tsum_congr
  intro s
  simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg (ne_of_gt s.2.1)]

theorem IsSemimartingale.quadraticVariation_of_finiteVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.quadraticVariation hF)
      (fun t ω ↦ (X 0 ω) ^ 2 + ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2) P := by
  filter_upwards [hX.quadraticVariation_on_finiteVariation_paths hF, hv] with ω h hvω
  exact h hvω

theorem IsSemimartingale.continuousQuadraticVariation_zero_on_finiteVariation_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (X · ω) univ → ∀ t : ℝ≥0,
      hX.continuousQuadraticVariation hF t ω = 0 := by
  filter_upwards [hX.quadraticVariation_on_finiteVariation_paths hF,
    hX.quadraticVariation_continuous_jump_decomposition hF] with ω hq hd hv t
  linarith [(hq hv t), (hd t).2]

theorem IsSemimartingale.continuousQuadraticVariation_zero_of_finiteVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.continuousQuadraticVariation hF) 0 P := by
  filter_upwards [hX.continuousQuadraticVariation_zero_on_finiteVariation_paths hF, hv]
    with ω h hvω
  exact h hvω

end ProbabilityTheory
