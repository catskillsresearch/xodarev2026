/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.UniformConvergence
public import StochLean.Probability.Process.Path.Monotone

/-! # Monotone paths and initial values under UCP limits

The subsequence supplied by UCP convergence converges locally uniformly on one
common full-measure event. Intersecting this event with the countably many
path-monotonicity events preserves order simultaneously at every pair of times.
No regularity, measurability, or integrability of the processes is required.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

private theorem tendsto_allTime_of_compactDeviation
    {k : ℕ → ℕ} {ω : Ω}
    (h : ∀ T : ℝ≥0,
      Tendsto (fun n ↦ compactDeviation (X (k n)) Y T ω) atTop (𝓝 0))
    (t : ℝ≥0) : Tendsto (fun n ↦ X (k n) t ω) atTop (𝓝 (Y t ω)) :=
  (tendsto_compactDeviation_iff_tendstoUniformlyOn.mp (h t)).tendsto_at
    ⟨bot_le, le_rfl⟩

/-- A UCP limit of processes with almost-sure monotone paths also has
almost-sure monotone paths, with one exceptional null set for all times. -/
theorem TendstoUCP.hasMonotonePaths (h : TendstoUCP P X atTop Y)
    (hm : ∀ n, HasMonotonePaths (X n) P) : HasMonotonePaths Y P := by
  obtain ⟨k, _, hk⟩ := h.exists_seq_ae_locallyUniform
  have hm' : ∀ᵐ ω ∂P, ∀ n, Monotone (fun t ↦ X (k n) t ω) :=
    ae_all_iff.mpr (fun n ↦ hm (k n))
  filter_upwards [hk, hm'] with ω hω hmω
  intro s t hst
  exact le_of_tendsto_of_tendsto'
    (tendsto_allTime_of_compactDeviation hω s)
    (tendsto_allTime_of_compactDeviation hω t)
    (fun n ↦ hmω n hst)

/-- A common initial value survives UCP convergence. The initial function can
be arbitrary: no measurability or integrability assumption is needed. -/
theorem TendstoUCP.ae_eq_initial (h : TendstoUCP P X atTop Y)
    {C : Ω → ℝ} (h0 : ∀ n, X n 0 =ᵐ[P] C) : Y 0 =ᵐ[P] C := by
  obtain ⟨k, _, hk⟩ := h.exists_seq_ae_locallyUniform
  have h0' : ∀ᵐ ω ∂P, ∀ n, X (k n) 0 ω = C ω :=
    ae_all_iff.mpr (fun n ↦ h0 (k n))
  filter_upwards [hk, h0'] with ω hω h0ω
  have hlim := tendsto_allTime_of_compactDeviation hω 0
  have hc : Tendsto (fun n ↦ X (k n) 0 ω) atTop (𝓝 (C ω)) := by
    simpa only [h0ω] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C ω) atTop (𝓝 (C ω)))
  exact tendsto_nhds_unique hlim hc

/-- A UCP limit of zero-initial processes with almost-sure monotone paths is
nonnegative at all times on one common full-measure event. -/
theorem TendstoUCP.ae_nonneg_of_monotone_zero (h : TendstoUCP P X atTop Y)
    (hm : ∀ n, HasMonotonePaths (X n) P)
    (h0 : ∀ n, X n 0 =ᵐ[P] (fun _ ↦ 0)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ Y t ω := by
  filter_upwards [h.hasMonotonePaths hm, h.ae_eq_initial h0] with ω hmω h0ω
  intro t
  simpa only [h0ω] using hmω (show (0 : ℝ≥0) ≤ t from bot_le)

end ProbabilityTheory
