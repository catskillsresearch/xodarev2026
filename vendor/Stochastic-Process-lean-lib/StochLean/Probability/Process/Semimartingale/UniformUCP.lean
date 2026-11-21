/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Maximal
public import StochLean.Probability.Process.UCP.DeviationEvents

/-! # Uniform source convergence gives UCP convergence of elementary integral processes

This proves the first, uniform-input half of Protter II.11 for ordinary semimartingales.
Convergence of the source inputs is uniform in both time and sample; general UCP-input
continuity still requires the separate caglad first-exit truncation argument.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.tendstoUCP_elementaryIntegralProcess_of_uniform_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {H : ℕ → ℝ≥0 → Ω → ℝ} (hH : ∀ n, IsSimplePredictable (H n) F)
    (hu : TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2) (fun _ ↦ 0) atTop) :
    TendstoUCP P (fun n ↦ (hH n).elementaryIntegralProcess X) atTop 0 := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  simp only [Pi.zero_apply, sub_zero]
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := hX.elementaryIntegralProcess_maximal_uniform hF T ε hε η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hu δ hδ)
  refine ⟨N, fun n hn ↦ hb (H n) (hH n) ?_⟩
  intro t ω
  simpa only [dist_zero_left] using (hN n hn (t, ω)).le

theorem IsSemimartingale.tendstoUCP_elementaryIntegralProcess_of_uniform
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {H : ℕ → ℝ≥0 → Ω → ℝ} {K : ℝ≥0 → Ω → ℝ}
    (hH : ∀ n, IsSimplePredictable (H n) F) (hK : IsSimplePredictable K F)
    (hu : TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2)
      (fun z ↦ K z.1 z.2) atTop) :
    TendstoUCP P (fun n ↦ (hH n).elementaryIntegralProcess X) atTop
      (hK.elementaryIntegralProcess X) := by
  have hd : TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2 - K z.1 z.2)
      (fun _ ↦ 0) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with n hn
    intro z
    simpa only [dist_zero_left, dist_eq_norm_sub, norm_sub_rev, sub_zero] using hn z
  have hj := hX.tendstoUCP_elementaryIntegralProcess_of_uniform_zero hF
    (fun n ↦ (hH n).sub hK) hd
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  have heq (n : ℕ) := (hH n).elementaryIntegralProcess_sub hK X
  have h := tendstoUCP_iff_measure_exists_norm_lt.mp hj T ε hε
  simpa only [heq, Pi.sub_apply, Pi.zero_apply, sub_zero] using h

end ProbabilityTheory
