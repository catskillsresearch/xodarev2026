/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesPureJumpIntegral
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationLocality

/-! # The actual stochastic integral against a pure-jump FV path

On the common-event source caglad domain, compact integrand bounds follow
from regularity. The formula retains the initial product and the actual
absolutely summable positive-time jump series. No expected variation or
sample-uniform integrand bound is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_pureJump_finiteVariation_on_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (X · ω) univ →
      (∀ t, X t ω - X 0 ω = ∑' s : Ioc 0 t, jumpProcess X s ω) → ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ |H s ω * jumpProcess X s ω|) ∧
      hX.stochasticIntegral hF ha hr t ω = H 0 ω * X 0 ω +
        ∑' s : Ioc 0 t, H s ω * jumpProcess X s ω := by
  filter_upwards [hX.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation hF ha hr, hr]
    with ω hI hH hv hj
  obtain ⟨hc, he⟩ := hI hv
  have hl (T : ℝ≥0) (s : Ioc 0 T) :
      leftLimitProcess X s ω = Function.leftLim (X · ω) s := by
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hpure (T : ℝ≥0) : X T ω - X 0 ω =
      ∑' s : Ioc 0 T, (X s ω - Function.leftLim (X · ω) s) := by
    simpa only [jumpProcess, Pi.sub_apply, hl T] using hj T
  intro t
  obtain ⟨C, _, hC⟩ := hH.exists_norm_bound_Icc t
  have hb (s : ℝ≥0) (hs : s ∈ Ioc 0 t) : ‖H s ω‖ ≤ C := hC s ⟨hs.1.le, hs.2⟩
  constructor
  · simpa only [jumpProcess, Pi.sub_apply, hl t] using
      summable_abs_weighted_jumps_of_locallyBoundedVariation hv hc.1 t hb
  · rw [he t]
    change H 0 ω * X 0 ω + pathStieltjesIncrementIntegral (X · ω) hv hc.1 (H · ω) 0 t = _
    rw [pathStieltjesIncrementIntegral_eq_tsum_of_pureJump_of_integrable hv hc.1 hpure t
        (hH.integrableOn_variationStieltjes hv hc.1 t) hb]
    simp only [jumpProcess, Pi.sub_apply, hl t]

theorem IsSemimartingale.stochasticIntegral_of_pureJump_finiteVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P)
    (hj : ∀ᵐ ω ∂P, ∀ t, X t ω - X 0 ω = ∑' s : Ioc 0 t, jumpProcess X s ω)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable (hX.stochasticIntegral hF ha hr)
      (fun t ω ↦ H 0 ω * X 0 ω + ∑' s : Ioc 0 t, H s ω * jumpProcess X s ω) P := by
  filter_upwards [hX.stochasticIntegral_pureJump_finiteVariation_on_paths hF ha hr, hv, hj]
    with ω hI hvω hjω t
  exact (hI hvω hjω t).2

end ProbabilityTheory
