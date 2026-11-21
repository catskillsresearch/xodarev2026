/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CadlagTaylorLimit
public import StochLean.Analysis.PathVariation.UniformSquareBound
public import StochLean.Probability.Process.Partition.TaylorSums
public import StochLean.Probability.Process.Semimartingale.Ito.JumpSummability

/-! # Identifying cadlag stochastic Taylor-error limits with the actual jump series

The raw bracket supplies bounded partial square sums on a nested uniform
subsequence. The deterministic cadlag theorem applies on one common event
at every finite time. No regularity or measurability of the proposed limit
process needs to be separately assumed.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Z : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticTaylorError_limit_eq_jump_series
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P)
    (hE : TendstoUCP P (fun n ↦ (π n).quadraticTaylorErrorProcess f X) atTop Z) :
    Indistinguishable Z (fun t ω ↦ ∑' s : Ioc 0 t,
      (f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
        deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)) P := by
  obtain ⟨k, hk, hkU⟩ :=
    (hX.tendstoUCP_quadraticVariationSumProcess hF hπ).exists_seq_ae_locallyUniform
  obtain ⟨l, hl, hlU⟩ := (hE.comp hk.tendsto_atTop).exists_seq_ae_locallyUniform
  filter_upwards [hkU, hlU, hπ, hX.hasCadlagPaths,
    hX.hasCadlagPaths_quadraticVariation hF, hX.summable_sq_jumps hF]
    with ω hQu hEu hπω hx hQω hsq
  have hm : Tendsto (fun n ↦ ((π (k (l n))).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      ((hπω.2.comp hk.tendsto_atTop).comp hl.tendsto_atTop)
  intro t
  have hT : ∀ᶠ n in atTop, t ≤ (π (k (l n))).terminal ω :=
    ((hπω.1.comp hk.tendsto_atTop).comp hl.tendsto_atTop).eventually (eventually_ge_atTop t)
  have hQ : TendstoUniformlyOn
      (fun n s ↦ X 0 ω ^ 2 + quadraticVariationSum ((π (k (l n))).path ω)
        (fun u ↦ X (min u s) ω))
      (hX.quadraticVariation hF · ω) atTop (Icc 0 t) :=
    tendsto_compactDeviation_iff_tendstoUniformlyOn.mp ((hQu t).comp hl.tendsto_atTop)
  obtain ⟨B, hB, hb⟩ := eventually_bound_partialSquareSums_of_uniform_limit
    (fun n ↦ (π (k (l n))).path ω) (x := (X · ω)) hQω hQ
  have hj (s : Ioc 0 t) : leftLimitProcess X s ω = Function.leftLim (X · ω) s := by
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hs : Summable (fun s : Ioc 0 t ↦ (X s ω - Function.leftLim (X · ω) s) ^ 2) := by
    simpa only [jumpProcess, Pi.sub_apply, hj] using hsq t
  have hd := tendsto_quadraticTaylorErrorSum_cadlag
    (fun n ↦ (π (k (l n))).path ω) hx hf hm hT hB
    (hb.mono (fun _ hn ↦ hn t ⟨bot_le, le_rfl⟩)) hs
  have he := (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hEu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  simpa only [jumpProcess, Pi.sub_apply, hj] using tendsto_nhds_unique he hd

end ProbabilityTheory
