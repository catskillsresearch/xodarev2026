/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.PartialSums

/-!
# Total variation of limiting covariation

Klenke 21.61(ii) on a fixed enclosing horizon. The limiting cross variation is
assumed at each partial terminal time, as in the source; no finite-variation
assumption is imposed on that limit. Its finite variation is a conclusion.
-/

@[expose] public section

open Filter Set
open scoped NNReal ENNReal Topology

namespace StochLean

variable {T : ℝ≥0} {π : ℕ → TimePartition T} {f g C : ℝ≥0 → ℝ} {a b : ℝ}

theorem eVariationOn_covariation_limit_le (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hfv : HasQuadraticVariationAlong π f a) (hgv : HasQuadraticVariationAlong π g b)
    (hC : ∀ s ≤ T,
      HasCovariationAlong π (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) (C s)) :
    eVariationOn C (Icc 0 T) ≤ ENNReal.ofReal (Real.sqrt a * Real.sqrt b) := by
  have hlim : ∀ s ∈ Icc 0 T,
      Tendsto (fun n ↦ completedCovariationSum (π n) f g s) atTop (𝓝 (C s)) :=
    fun s hs ↦ tendsto_completedCovariationSum_of_partial hf hg hmesh hs.2 (hC s hs.2)
  have hb : Tendsto (fun n ↦ ENNReal.ofReal
      (Real.sqrt (quadraticVariationSum (π n) f) * Real.sqrt (quadraticVariationSum (π n) g)))
      atTop (𝓝 (ENNReal.ofReal (Real.sqrt a * Real.sqrt b))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuous_sqrt.continuousAt.tendsto.comp hfv).mul
        (Real.continuous_sqrt.continuousAt.tendsto.comp hgv))
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  apply ge_of_tendsto hb
  filter_upwards [eVariationOn.lowerSemicontinuous_aux hlim hc] with n hn
  exact hn.le.trans (eVariationOn_completedCovariationSum_le (π n) f g (Icc 0 T))

theorem boundedVariationOn_covariation_limit (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hfv : HasQuadraticVariationAlong π f a) (hgv : HasQuadraticVariationAlong π g b)
    (hC : ∀ s ≤ T,
      HasCovariationAlong π (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) (C s)) :
    BoundedVariationOn C (Icc 0 T) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (eVariationOn_covariation_limit_le hf hg hmesh hfv hgv hC)

end StochLean
