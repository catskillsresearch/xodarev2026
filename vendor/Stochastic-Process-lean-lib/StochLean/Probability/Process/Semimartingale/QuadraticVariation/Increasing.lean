/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Riemann
public import StochLean.Probability.Process.Semimartingale.FiniteVariation
public import StochLean.Probability.Process.Path.UniformRightEvaluation
public import StochLean.Probability.Process.Partition.Klenke
public import StochLean.Analysis.PathVariation.CeilingSquareSums
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # Increasing paths of the canonical raw quadratic variation

The partial-cell square sums are not assumed monotone. Evaluating each sum
at the next partition endpoint produces monotone completed-cell sums. A
locally uniform subsequence and right continuity identify their pointwise
limit with the raw bracket on one event for all times together.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.hasMonotonePaths_quadraticVariation_of_partition
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    HasMonotonePaths (hX.quadraticVariation hF) P := by
  obtain ⟨k, hk, hU⟩ :=
    (hX.tendstoUCP_quadraticVariationSumProcess hF hπ).exists_seq_ae_locallyUniform
  filter_upwards [hπ, hU, hX.hasCadlagPaths_quadraticVariation hF] with ω hπω hu hQ
  have hT : Tendsto (fun n ↦ (π (k n)).terminal ω) atTop atTop := hπω.1.comp hk.tendsto_atTop
  have hm : Tendsto (fun n ↦ ((π (k n)).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (hπω.2.comp hk.tendsto_atTop)
  have heval (s : ℝ≥0) : Tendsto (fun n ↦ (π (k n)).quadraticVariationSumProcess X
      (((π (k n)).path ω).ceilingPoint s) ω) atTop (𝓝 (hX.quadraticVariation hF s ω)) := by
    apply tendsto_eval_of_locallyUniform_of_tendsto_nhdsGE
      (fun T ↦ tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hu T)) hQ.1
    exact StochLean.TimePartition.ceilingPoint_tendsto_nhdsGE_of_eventually_le
      (fun n ↦ (π (k n)).path ω) s (hT.eventually (eventually_ge_atTop s)) hm
  intro s t hst
  apply le_of_tendsto_of_tendsto (heval s) (heval t)
  apply Eventually.of_forall
  intro n
  exact add_le_add le_rfl (StochLean.monotone_quadraticVariationSum_stop_ceilingPoint
    ((π (k n)).path ω) (X · ω) hst)

theorem IsSemimartingale.hasMonotonePaths_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasMonotonePaths (hX.quadraticVariation hF) P := by
  apply hX.hasMonotonePaths_quadraticVariation_of_partition hF
    (StoppingTimePartition.isTendingToIdentity_of_klenke
      StochLean.LocallyFinitePartition.dyadic_admissible
      (T := fun n ↦ (n : ℝ≥0)) tendsto_natCast_atTop_atTop)

theorem IsSemimartingale.initial_sq_le_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t, (X 0 ω) ^ 2 ≤ hX.quadraticVariation hF t ω := by
  filter_upwards [hX.hasMonotonePaths_quadraticVariation hF, hX.quadraticVariation_zero_ae hF]
    with ω hm h0 t
  exact h0 ▸ hm (show (0 : ℝ≥0) ≤ t from bot_le)

theorem IsSemimartingale.hasFiniteVariationPaths_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (hX.quadraticVariation hF) P :=
  (hX.hasMonotonePaths_quadraticVariation hF).hasFiniteVariationPaths

theorem IsSemimartingale.isSemimartingale_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.quadraticVariation hF) F P :=
  (hX.hasFiniteVariationPaths_quadraticVariation hF).isSemimartingale
    (hX.adapted_quadraticVariation hF) hF (hX.hasCadlagPaths_quadraticVariation hF)

end ProbabilityTheory
