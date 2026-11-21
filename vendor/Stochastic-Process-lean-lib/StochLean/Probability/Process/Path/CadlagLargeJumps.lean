/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagFiniteOscillation
public import Mathlib.Data.Finset.Max

/-! # Actual large jumps of cadlag paths are locally finite

A compact cadlag path has only finitely many positive-time jumps larger than
any fixed positive threshold. The proof first finds finitely many oscillation
separators, then proves that every large jump is among them. The separators
are not asserted to be jumps themselves.

The finite set also supplies an actual earliest large jump after a given
finite time, whenever any such jump exists. These are pathwise assertions;
no measurability or stopping-time property of the earliest jump is claimed.
The initial source jump is deliberately excluded.
-/

@[expose] public section

open Filter Set Metric
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.finite_large_jumps_Ioc (hX : IsCadlagPath (X · ω))
    (T : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ b < ‖jumpProcess X t ω‖}.Finite := by
  classical
  obtain ⟨A, _, δ, hδ, hosc⟩ := hX.exists_finite_separators_oscillation T hb
  apply A.finite_toSet.subset
  rintro t ⟨ht, htT, hj⟩
  by_contra htA
  have havoid : ∀ᶠ s in 𝓝[<] t, ∀ a ∈ A, a ∉ Ioc s t := by
    apply A.eventually_all.mpr
    intro a ha
    by_cases hat : a ≤ t
    · have halt : a < t := lt_of_le_of_ne hat (fun he ↦ htA (he ▸ ha))
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds halt)] with s hs
      exact fun hmem ↦ (not_lt_of_ge (show a ≤ s from (show a < s from hs).le)) hmem.1
    · exact Eventually.of_forall fun s hmem ↦ hat hmem.2
  have hd : ∀ᶠ s in 𝓝[<] t, dist s t < δ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)
  have hbound : ∀ᶠ s in 𝓝[<] t, ‖X t ω - X s ω‖ ≤ b := by
    filter_upwards [havoid, hd, self_mem_nhdsWithin] with s hs hst hlt
    have hsle : s ≤ t := (show s < t from hlt).le
    have h := hosc s ⟨bot_le, hsle.trans htT⟩ t ⟨bot_le, htT⟩ hsle hst hs
    simpa only [dist_eq_norm, norm_sub_rev] using h.le
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hlim : Tendsto (fun s ↦ ‖X t ω - X s ω‖) (𝓝[<] t)
      (𝓝 ‖X t ω - leftLimitProcess X t ω‖) :=
    (tendsto_const_nhds.sub (hX.tendsto_leftLimitProcess ht.ne')).norm
  have hle : ‖jumpProcess X t ω‖ ≤ b := le_of_tendsto hlim hbound
  exact (not_le_of_gt hj) hle

/-- A positive inclusive jump threshold is locally finite as well. -/
theorem IsCadlagPath.finite_jumps_ge_Ioc (hX : IsCadlagPath (X · ω))
    (T : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ b ≤ ‖jumpProcess X t ω‖}.Finite := by
  apply (hX.finite_large_jumps_Ioc T (half_pos hb)).subset
  rintro t ⟨ht, htT, hj⟩
  exact ⟨ht, htT, (half_lt_self hb).trans_le hj⟩

/-- The finite list is exactly the actual large-jump set, not a list of
possibly extraneous oscillation separators. -/
theorem IsCadlagPath.exists_finset_large_jumps_Ioc (hX : IsCadlagPath (X · ω))
    (T : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    ∃ A : Finset ℝ≥0, ∀ t, t ∈ A ↔ 0 < t ∧ t ≤ T ∧ b < ‖jumpProcess X t ω‖ := by
  classical
  refine ⟨(hX.finite_large_jumps_Ioc T hb).toFinset, ?_⟩
  intro t
  exact (hX.finite_large_jumps_Ioc T hb).mem_toFinset

/-- Local finiteness supplies an actual first large jump strictly after `s`.
No value at infinity and no stopping-time assertion is introduced here. -/
theorem IsCadlagPath.exists_first_large_jump_after (hX : IsCadlagPath (X · ω))
    (s : ℝ≥0) {b : ℝ} (hb : 0 < b)
    (hex : ∃ t : ℝ≥0, s < t ∧ b < ‖jumpProcess X t ω‖) :
    ∃ t : ℝ≥0, s < t ∧ b < ‖jumpProcess X t ω‖ ∧
      ∀ u : ℝ≥0, s < u → b < ‖jumpProcess X u ω‖ → t ≤ u := by
  classical
  obtain ⟨T, hsT, hT⟩ := hex
  have hf : {t : ℝ≥0 | s < t ∧ t ≤ T ∧ b < ‖jumpProcess X t ω‖}.Finite := by
    apply (hX.finite_large_jumps_Ioc T hb).subset
    rintro t ⟨hst, htT, ht⟩
    exact ⟨lt_of_le_of_lt bot_le hst, htT, ht⟩
  let A := hf.toFinset
  have hAmem (t : ℝ≥0) : t ∈ A ↔ s < t ∧ t ≤ T ∧ b < ‖jumpProcess X t ω‖ :=
    hf.mem_toFinset
  have hA : A.Nonempty := ⟨T, (hAmem T).mpr ⟨hsT, le_rfl, hT⟩⟩
  have hm := (hAmem (A.min' hA)).mp (Finset.min'_mem A hA)
  refine ⟨A.min' hA, hm.1, hm.2.2, fun u hsu hu ↦ ?_⟩
  by_cases huT : u ≤ T
  · exact Finset.min'_le A u ((hAmem u).mpr ⟨hsu, huT, hu⟩)
  · exact hm.2.1.trans (le_of_not_ge huT)

end ProbabilityTheory
