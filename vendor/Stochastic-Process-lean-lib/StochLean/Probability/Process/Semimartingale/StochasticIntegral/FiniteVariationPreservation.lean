/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationLocality

/-! # Finite variation is preserved by Chapter II stochastic integration

This is the remark following Protter II.19, also on individual FV paths up to
one null set. Compact caglad bounds give pathwise integrability; no expected
variation, bounded coefficients or global total variation is required.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_finiteVariation_on_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (X · ω) univ →
      LocallyBoundedVariationOn (hX.stochasticIntegral hF ha hr · ω) univ := by
  filter_upwards [hX.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation hF ha hr, hr]
    with ω hI hH
  intro hv
  obtain ⟨hXω, heq⟩ := hI hv
  rw [show (hX.stochasticIntegral hF ha hr · ω) =
    pathStieltjesIntegral (X · ω) hv hXω.1 (H · ω) from funext heq]
  exact locallyBoundedVariationOn_pathStieltjesIntegral
    (fun T ↦ hH.integrableOn_variationStieltjes hv hXω.1 T)

theorem IsSemimartingale.hasFiniteVariationPaths_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    HasFiniteVariationPaths (hX.stochasticIntegral hF ha hr) P := by
  filter_upwards [hX.stochasticIntegral_finiteVariation_on_paths hF ha hr, hv] with ω hI hXω
  exact hI hXω

end ProbabilityTheory
