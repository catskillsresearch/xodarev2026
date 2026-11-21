/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.UniformSquareBound
public import StochLean.Probability.Process.Partition.TaylorSums
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Increasing

/-! # Vanishing quadratic Taylor errors for continuous semimartingales

Two nested subsequences give uniform convergence of the actual square sums
and the error processes on one event for every compact time interval. The
deterministic Taylor estimate then identifies any UCP limit with zero.
No monotonicity of partial-cell square sums is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Z : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticTaylorError_limit_zero_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P)
    (hE : TendstoUCP P (fun n ↦ (π n).quadraticTaylorErrorProcess f X) atTop Z) :
    Indistinguishable Z 0 P := by
  obtain ⟨k, hk, hkU⟩ :=
    (hX.tendstoUCP_quadraticVariationSumProcess hF hπ).exists_seq_ae_locallyUniform
  obtain ⟨l, hl, hlU⟩ := (hE.comp hk.tendsto_atTop).exists_seq_ae_locallyUniform
  filter_upwards [hkU, hlU, hπ, hc, hX.hasCadlagPaths_quadraticVariation hF]
    with ω hQu hEu hπω hXω hQω
  have hm : Tendsto (fun n ↦ ((π (k (l n))).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      ((hπω.2.comp hk.tendsto_atTop).comp hl.tendsto_atTop)
  intro t
  have hQ : TendstoUniformlyOn
      (fun n s ↦ X 0 ω ^ 2 + quadraticVariationSum ((π (k (l n))).path ω)
        (fun u ↦ X (min u s) ω))
      (hX.quadraticVariation hF · ω) atTop (Icc 0 t) :=
    tendsto_compactDeviation_iff_tendstoUniformlyOn.mp ((hQu t).comp hl.tendsto_atTop)
  obtain ⟨B, hB, hb⟩ := eventually_bound_partialSquareSums_of_uniform_limit
    (fun n ↦ (π (k (l n))).path ω) (x := (X · ω)) hQω hQ
  have hzero := tendstoUniformlyOn_quadraticTaylorErrorSum_zero
    (fun n ↦ (π (k (l n))).path ω) hXω.continuousOn hf hm hB hb
  have he := (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hEu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  exact tendsto_nhds_unique he (hzero.tendsto_at ⟨bot_le, le_rfl⟩)

end ProbabilityTheory
