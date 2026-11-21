/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Subtraction
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.PathwiseIntegral

/-! # Protter II.18: locality on events of path agreement

The actual density construction preserves zero input paths. Uniform limits
therefore retain zero integral paths on that event, up to one null set. Linearity
gives integrand locality; common approximants give integrator locality. There is
no assumption that the agreement event is known at time zero or has full measure.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H K : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_zero_on_zero_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, (∀ t, H t ω = 0) → ∀ t, hX.stochasticIntegral hF ha hr t ω = 0 := by
  obtain ⟨S, hS, hzS, huS⟩ := exists_simplePredictable_tendstoUCP_preserves_zero_paths ha hF hr
  obtain ⟨k, _, hkU⟩ :=
    (hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS).exists_seq_ae_locallyUniform
  filter_upwards [hkU] with ω hJu
  intro hz t
  have hj := (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hJu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  have heq (n : ℕ) : (hS (k n)).elementaryIntegralProcess X t ω = 0 :=
    (hS (k n)).elementaryIntegralProcess_eq_zero_of_zero_path (hzS (k n) ω hz) X t
  simp only [heq] at hj
  exact tendsto_nhds_unique hj tendsto_const_nhds

theorem IsSemimartingale.stochasticIntegral_congr_integrand_on_paths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    ∀ᵐ ω ∂P, (∀ t, H t ω = K t ω) → ∀ t,
      hX.stochasticIntegral hF haH hrH t ω = hX.stochasticIntegral hF haK hrK t ω := by
  filter_upwards [hX.stochasticIntegral_zero_on_zero_paths hF
    (fun t ↦ (haH t).sub (haK t)) (hrH.sub hrK),
    hX.stochasticIntegral_sub hF haH hrH haK hrK] with ω hzero hsub
  intro hHK t
  have hz := hzero (fun s ↦ sub_eq_zero.mpr (hHK s)) t
  exact sub_eq_zero.mp ((hsub t).symm.trans hz)

theorem IsSemimartingale.stochasticIntegral_congr_integrator_on_paths
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∀ᵐ ω ∂P, (∀ t, X t ω = Y t ω) → ∀ t,
      hX.stochasticIntegral hF ha hr t ω = hY.stochasticIntegral hF ha hr t ω := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  have huX := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  have huY := hY.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  obtain ⟨k, hk, hkU⟩ := huX.exists_seq_ae_locallyUniform
  obtain ⟨l, hl, hlU⟩ := (huY.comp hk.tendsto_atTop).exists_seq_ae_locallyUniform
  filter_upwards [hkU, hlU] with ω hXu hYu
  intro hXY t
  have hx := ((tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hXu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)).comp hl.tendsto_atTop
  have hy := (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (hYu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  change Tendsto (fun n ↦ (hS (k (l n))).elementaryIntegralProcess X t ω) atTop
    (𝓝 (hX.stochasticIntegral hF ha hr t ω)) at hx
  change Tendsto (fun n ↦ (hS (k (l n))).elementaryIntegralProcess Y t ω) atTop
    (𝓝 (hY.stochasticIntegral hF ha hr t ω)) at hy
  have heq (n : ℕ) : (hS (k (l n))).elementaryIntegralProcess X t ω =
      (hS (k (l n))).elementaryIntegralProcess Y t ω :=
    (hS (k (l n))).elementaryIntegralProcess_congr_integrator_path hXY t
  simp only [heq] at hx
  exact tendsto_nhds_unique hx hy

/-- Local behavior on the event where both the integrand and the integrator paths agree. -/
theorem IsSemimartingale.stochasticIntegral_congr_on_paths
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    ∀ᵐ ω ∂P, (∀ t, H t ω = K t ω) → (∀ t, X t ω = Y t ω) → ∀ t,
      hX.stochasticIntegral hF haH hrH t ω = hY.stochasticIntegral hF haK hrK t ω := by
  filter_upwards [hX.stochasticIntegral_congr_integrand_on_paths hF haH hrH haK hrK,
    hX.stochasticIntegral_congr_integrator_on_paths hY hF haK hrK] with ω hHK hXY
  intro hH hX t
  exact (hHK hH t).trans (hXY hX t)

end ProbabilityTheory
