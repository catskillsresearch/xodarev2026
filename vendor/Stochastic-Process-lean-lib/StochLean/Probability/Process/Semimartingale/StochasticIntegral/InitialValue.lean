/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral

/-! # The source initial term of the constructed integral

The integral starts at `H_0 X_0`, with no integrability or boundedness assumption
on either factor. Actual almost-sure subsequences transfer the elementary identity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_zero_ae
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    hX.stochasticIntegral hF ha hr 0 =ᵐ[P] fun ω ↦ H 0 ω * X 0 ω := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  have hJS := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  obtain ⟨k, hk, hkU⟩ := huS.exists_seq_ae_locallyUniform
  obtain ⟨l, hl, hlU⟩ := (hJS.comp hk.tendsto_atTop).exists_seq_ae_locallyUniform
  filter_upwards [hkU, hlU] with ω hSu hJu
  have hs : Tendsto (fun n ↦ S (k (l n)) 0 ω) atTop (𝓝 (H 0 ω)) :=
    ((tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hSu 0)).tendsto_at
      ⟨le_rfl, le_rfl⟩).comp hl.tendsto_atTop
  have hj : Tendsto (fun n ↦ (hS (k (l n))).elementaryIntegralProcess X 0 ω) atTop
      (𝓝 (hX.stochasticIntegral hF ha hr 0 ω)) :=
    (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hJu 0)).tendsto_at ⟨le_rfl, le_rfl⟩
  simp only [IsSimplePredictable.elementaryIntegralProcess_zero] at hj
  exact tendsto_nhds_unique hj (hs.mul_const (X 0 ω))

end ProbabilityTheory
