/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationLocality
public import StochLean.Analysis.PathVariation.IncreasingIntegral

/-! # Integration preserves increasing paths for nonnegative integrands

The statement concerns the actual Chapter II integral on one common event.
Neither expected variation nor initial integrability is required.
-/

@[expose] public section

open MeasureTheory Filter StochLean Set
open scoped NNReal

namespace ProbabilityTheory

theorem IsSemimartingale.hasMonotonePaths_stochasticIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hx : HasMonotonePaths X P) (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hH : ∀ᵐ ω ∂P, ∀ t, 0 ≤ H t ω) :
    HasMonotonePaths (hX.stochasticIntegral hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation hF ha hr,
    hx, hr, hH] with ω he hm hω hpos
  let hv := (hm.monotoneOn univ).locallyBoundedVariationOn
  obtain ⟨hc, heq⟩ := he hv
  have hi := monotone_pathStieltjesIntegral_of_nonneg hm hc.1 hv
    (fun T ↦ hω.integrableOn_variationStieltjes hv hc.1 T) hpos
  intro s t hst
  simpa only [heq] using hi hst

end ProbabilityTheory
