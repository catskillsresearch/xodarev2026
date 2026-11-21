/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.VectorTaylorLimit
public import StochLean.Analysis.PathVariation.UniformVectorSquareBound
public import StochLean.Probability.Process.Partition.VectorTaylorSums
public import StochLean.Probability.Process.Semimartingale.Ito.VectorJumpSummability
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Riemann
public import StochLean.Probability.Process.UCP.FiniteSum

/-! # Identifying vector stochastic Taylor errors on one common event

One uniform subsequence of the sum of the original coordinate raw-square
approximations bounds vector energy. A nested error subsequence then identifies
every finite-time limit with the actual summable Frechet jump correction.
-/

@[expose] public section

open MeasureTheory Filter Set Finset StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ} {Z : ℝ≥0 → Ω → ℝ}

theorem frechetTaylorError_limit_eq_jump_series
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P)
    (hE : TendstoUCP P (fun n ↦ (π n).frechetTaylorErrorProcess f X) atTop Z) :
    Indistinguishable Z (fun t ω ↦ ∑' s : Ioc 0 t,
      frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
        (fun i ↦ X i s ω)) P := by
  have hUQ := TendstoUCP.sum univ
    (fun i _ ↦ (hX i).tendstoUCP_quadraticVariationSumProcess hF hπ)
  obtain ⟨k, hk, hkU⟩ := hUQ.exists_seq_ae_locallyUniform
  obtain ⟨l, hl, hlU⟩ := (hE.comp hk.tendsto_atTop).exists_seq_ae_locallyUniform
  have hcQ : ∀ᵐ ω ∂P, ∀ i, IsCadlagPath ((hX i).quadraticVariation hF · ω) :=
    ae_all_iff.mpr (fun i ↦ (hX i).hasCadlagPaths_quadraticVariation hF)
  filter_upwards [hkU, hlU, hπ, HasCadlagPaths.pi (fun i ↦ (hX i).hasCadlagPaths),
    hcQ, summable_norm_sq_semimartingale_coordinate_jumps hX hF]
    with ω hQu hEu hπω hx hQpaths hsq
  have hm : Tendsto (fun n ↦ ((π (k (l n))).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      ((hπω.2.comp hk.tendsto_atTop).comp hl.tendsto_atTop)
  have hQω : IsCadlagPath (fun s ↦ ∑ i, (hX i).quadraticVariation hF s ω) :=
    IsCadlagPath.finset_sum univ (fun i s ↦ (hX i).quadraticVariation hF s ω)
      (fun i _ ↦ hQpaths i)
  intro t
  have hT : ∀ᶠ n in atTop, t ≤ (π (k (l n))).terminal ω :=
    ((hπω.1.comp hk.tendsto_atTop).comp hl.tendsto_atTop).eventually (eventually_ge_atTop t)
  have hQ : TendstoUniformlyOn
      (fun n s ↦ ∑ i, (X i 0 ω ^ 2 + quadraticVariationSum ((π (k (l n))).path ω)
        (fun u ↦ X i (min u s) ω)))
      (fun s ↦ ∑ i, (hX i).quadraticVariation hF s ω) atTop (Icc 0 t) := by
    simpa only [Finset.sum_apply, StoppingTimePartition.quadraticVariationSumProcess] using
      (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp ((hQu t).comp hl.tendsto_atTop))
  obtain ⟨B, hB, hb⟩ := eventually_bound_partialVectorSquareSums_of_uniform_limit
    (fun n ↦ (π (k (l n))).path ω) (x := fun s i ↦ X i s ω) hQω hQ
  have hleft (s : Ioc 0 t) : Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ leftLimitProcess (X i) s ω := by
    rw [hx.leftLim_pi]
    funext i
    simp only [leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hj (s : Ioc 0 t) : (fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ jumpProcess (X i) s ω := by rw [hleft]; rfl
  have hs : Summable (fun s : Ioc 0 t ↦
      ‖(fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s‖ ^ 2) := by
    simpa only [hj] using hsq t
  have hd := tendsto_frechetTaylorErrorSum_cadlag
    (fun n ↦ (π (k (l n))).path ω) hx hf hm hT hB
    (hb.mono (fun _ hn ↦ hn t ⟨bot_le, le_rfl⟩)) hs
  have he := (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hEu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  simpa only [hleft] using tendsto_nhds_unique he hd

end ProbabilityTheory
