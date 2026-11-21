/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.PartialSums
public import Mathlib.Topology.Order.IsLUB

/-! # All-times extraction through monotone completed-cell sums

Monotonicity in time belongs to the completed-cell sums, not to the sums with a moving
terminal partial cell. Dense convergence extends to every time only after this distinction.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean

theorem tendsto_monotone_of_dense {T : ℝ≥0} {D : Set ℝ≥0} (hD : Dense D)
    {F : ℕ → ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ} (hF : ∀ n, MonotoneOn (F n) (Icc 0 T))
    (hA : ContinuousOn A (Icc 0 T))
    (h0 : Tendsto (fun n ↦ F n 0) atTop (𝓝 (A 0)))
    (hT : Tendsto (fun n ↦ F n T) atTop (𝓝 (A T)))
    (hd : ∀ q ∈ D, q ≤ T → Tendsto (fun n ↦ F n q) atTop (𝓝 (A q)))
    {s : ℝ≥0} (hs : s ≤ T) : Tendsto (fun n ↦ F n s) atTop (𝓝 (A s)) := by
  by_cases hs0 : s = 0
  · simpa only [hs0] using h0
  by_cases hsT : s = T
  · simpa only [hsT] using hT
  have hpos : 0 < s := pos_iff_ne_zero.mpr hs0
  have hlt : s < T := lt_of_le_of_ne hs hsT
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨u, _, hu, hlim⟩ := hD.exists_seq_strictMono_tendsto_of_lt hpos
    have hAlim : Tendsto (fun k ↦ A (u k)) atTop (𝓝 (A s)) :=
      (hA s ⟨bot_le, hs⟩).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hlim, Eventually.of_forall (fun k ↦ ⟨bot_le, (hu k).1.2.le.trans hs⟩)⟩)
    obtain ⟨k, hk⟩ := (hAlim.eventually_const_lt ha).exists
    filter_upwards [(hd (u k) (hu k).2 ((hu k).1.2.le.trans hs)).eventually_const_lt hk]
      with n hn
    exact hn.trans_le (hF n ⟨bot_le, (hu k).1.2.le.trans hs⟩ ⟨bot_le, hs⟩ (hu k).1.2.le)
  · intro b hb
    obtain ⟨u, _, hu, hlim⟩ := hD.exists_seq_strictAnti_tendsto_of_lt hlt
    have hAlim : Tendsto (fun k ↦ A (u k)) atTop (𝓝 (A s)) :=
      (hA s ⟨bot_le, hs⟩).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hlim, Eventually.of_forall (fun k ↦ ⟨bot_le, (hu k).1.2.le⟩)⟩)
    obtain ⟨k, hk⟩ := (hAlim.eventually_lt_const hb).exists
    filter_upwards [(hd (u k) (hu k).2 (hu k).1.2.le).eventually_lt_const hk] with n hn
    exact (hF n ⟨bot_le, hs⟩ ⟨bot_le, (hu k).1.2.le⟩ (hu k).1.1.le).trans_lt hn

@[simp] theorem completedCovariationSum_self {T : ℝ≥0} (π : TimePartition T)
    (f : ℝ≥0 → ℝ) : completedCovariationSum π f f = completedQuadraticVariationSum π f := by
  simp only [completedCovariationSum, completedQuadraticVariationSum, pow_two]

@[simp] theorem completedQuadraticVariationSum_zero {T : ℝ≥0} (π : TimePartition T)
    (f : ℝ≥0 → ℝ) : completedQuadraticVariationSum π f 0 = 0 := by
  unfold completedQuadraticVariationSum cumulativeStepSum
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : π.right i ≤ 0
  · have hr : π.right i = 0 := le_antisymm hi bot_le
    have hl : π.left i = 0 := le_antisymm ((π.left_le_right i).trans hi) bot_le
    simp [TimePartition.increment, hl, hr]
  · simp [hi]

theorem tendsto_partialQuadraticVariation_error_zero {T : ℝ≥0} {π : ℕ → TimePartition T}
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) {s : ℝ≥0} (hs : s ≤ T) :
    Tendsto (fun n ↦ quadraticVariationSum (π n) (fun t ↦ f (min t s)) -
      completedQuadraticVariationSum (π n) f s) atTop (𝓝 0) := by
  simpa only [covariationSum_self, completedCovariationSum_self] using
    tendsto_partialCovariation_error_zero hf hf hmesh hs

theorem tendsto_completedQuadraticVariationSum_of_partial {T : ℝ≥0}
    {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) {s : ℝ≥0} (hs : s ≤ T)
    {c : ℝ} (hc : HasQuadraticVariationAlong π (fun t ↦ f (min t s)) c) :
    Tendsto (fun n ↦ completedQuadraticVariationSum (π n) f s) atTop (𝓝 c) := by
  simpa only [sub_sub_cancel, sub_zero] using hc.sub
    (tendsto_partialQuadraticVariation_error_zero hf hmesh hs)

end StochLean
