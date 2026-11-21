/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessJump
public import StochLean.Probability.Process.Path.LeftLimitUniform

/-! # Protter II.13: jumps of the constructed stochastic integral

Two actual subsequences give simultaneous locally uniform convergence of the
simple integrands and their integral processes on one full-measure event.
Uniform control also transfers strict-left limits, so the identity holds at all
times together, including the separate source jump at zero.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.jumpProcess_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable (jumpProcess (hX.stochasticIntegral hF ha hr))
      (fun t ω ↦ H t ω * jumpProcess X t ω) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  have hJS := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  obtain ⟨k, hk, hkU⟩ := huS.exists_seq_ae_locallyUniform
  obtain ⟨l, hl, hlU⟩ := (hJS.comp hk.tendsto_atTop).exists_seq_ae_locallyUniform
  filter_upwards [hkU, hlU, hX.hasCadlagPaths] with ω hSu hJu hXω
  intro t
  have hs : Tendsto (fun n ↦ S (k (l n)) t ω) atTop (𝓝 (H t ω)) :=
    ((tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hSu t)).tendsto_at
      ⟨bot_le, le_rfl⟩).comp hl.tendsto_atTop
  have hj : Tendsto (fun n ↦ jumpProcess ((hS (k (l n))).elementaryIntegralProcess X) t ω)
      atTop (𝓝 (jumpProcess (hX.stochasticIntegral hF ha hr) t ω)) :=
    tendsto_jumpProcess_of_uniformlyOn
      (fun n ↦ (hS (k (l n))).isCadlagPath_elementaryIntegralProcess hXω)
      (hX.isCadlagPath_stochasticIntegral hF ha hr ω)
      (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hJu t))
  simp only [IsSimplePredictable.jumpProcess_elementaryIntegralProcess _ hXω] at hj
  exact tendsto_nhds_unique hj (hs.mul_const (jumpProcess X t ω))

end ProbabilityTheory
