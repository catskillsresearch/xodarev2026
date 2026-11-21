/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.FiniteVariation.PathwiseSimpleAgreement
public import StochLean.Analysis.PathVariation.StieltjesIntegralContinuity

/-! # Protter II.18: local agreement on finite-variation sample paths

On one full-measure event, every finite-variation path of the integrator gives
the original pathwise Stieltjes integral. The finite-variation event need not
have full or positive probability, and no conditional measure or usualness for
a conditioned measure is assumed. The proof uses actual uniform subsequences.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_eq_pathStieltjesIntegral_on_finiteVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, ∀ hv : LocallyBoundedVariationOn (X · ω) univ,
      ∃ hωr : IsCadlagPath (X · ω), ∀ t,
        hX.stochasticIntegral hF ha hr t ω =
          pathStieltjesIntegral (X · ω) hv hωr.1 (H · ω) t := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  have hJS := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  obtain ⟨k, hk, hkU⟩ := huS.exists_seq_ae_locallyUniform
  obtain ⟨l, hl, hlU⟩ := (hJS.comp hk.tendsto_atTop).exists_seq_ae_locallyUniform
  filter_upwards [hkU, hlU, hX.hasCadlagPaths, hr] with ω hSu hJu hXω hHω
  intro hv
  refine ⟨hXω, fun t ↦ ?_⟩
  have hs : TendstoUniformlyOn (fun n s ↦ S (k (l n)) s ω) (H · ω) atTop (Icc 0 t) :=
    tendsto_compactDeviation_iff_tendstoUniformlyOn.mp ((hSu t).comp hl.tendsto_atTop)
  have hi := tendstoUniformlyOn_pathStieltjesIntegral
    (fun n ↦ ((hS (k (l n))).isCagladPath ω).integrableOn_variationStieltjes hv hXω.1 t)
    (hHω.integrableOn_variationStieltjes hv hXω.1 t) hs
  have hj := (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hJu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  change Tendsto (fun n ↦ (hS (k (l n))).elementaryIntegralProcess X t ω) atTop
    (𝓝 (hX.stochasticIntegral hF ha hr t ω)) at hj
  have heq (n : ℕ) : (hS (k (l n))).elementaryIntegralProcess X t ω =
      pathStieltjesIntegral (X · ω) hv hXω.1 (S (k (l n)) · ω) t :=
    ((hS (k (l n))).pathStieltjesIntegral_eq_elementaryIntegralProcess hv hXω.1 t).symm
  simp only [heq] at hj
  exact tendsto_nhds_unique hj (hi.tendsto_at ⟨bot_le, le_rfl⟩)

end ProbabilityTheory
