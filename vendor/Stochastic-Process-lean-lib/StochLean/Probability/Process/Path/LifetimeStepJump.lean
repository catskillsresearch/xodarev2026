/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightStep
public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # Exact source jumps of lifetime step processes

A step activated on the closed lifetime event has left limit activated on the strict lifetime
event. Its jump is the coefficient on the lifetime graph and zero elsewhere. These formulas hold
also at zero, since the source convention is `leftLimitProcess X 0 = 0`, and an infinite lifetime
never activates at a finite time. Finite sums retain exactly the sum of their coincident jumps;
no disjointness assumption or artificial finite value for an infinite lifetime is needed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The strict-left value of a deterministic right step, including the source value at zero. -/
theorem leftLimitProcess_step_Ici (a : ℝ≥0) (Z : Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    leftLimitProcess (fun s v ↦ if a ≤ s then Z v else 0) t ω =
      if a < t then Z ω else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLimitProcess_zero, Pi.zero_apply, not_lt_zero, if_false]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [leftLimitProcess, if_neg ht]
    by_cases ha : a < t
    · rw [if_pos ha]
      apply leftLim_eq_of_tendsto
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with s hs
      exact (if_pos (show a ≤ s from (show a < s from hs).le)).symm
    · rw [if_neg ha]
      apply leftLim_eq_of_tendsto
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_neg (not_le_of_gt
        ((show s < t from hs).trans_le (le_of_not_gt ha)))).symm

/-- A deterministic right step jumps exactly at its activation time,
including activation at zero. -/
theorem jumpProcess_step_Ici (a : ℝ≥0) (Z : Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    jumpProcess (fun s v ↦ if a ≤ s then Z v else 0) t ω =
      if a = t then Z ω else 0 := by
  change (if a ≤ t then Z ω else 0) -
    leftLimitProcess (fun s v ↦ if a ≤ s then Z v else 0) t ω = _
  rw [leftLimitProcess_step_Ici]
  rcases lt_trichotomy a t with ha | ha | ha
  · simp only [if_pos ha.le, if_pos ha, if_neg ha.ne, sub_self]
  · subst t
    simp only [le_refl, if_true, lt_self_iff_false, if_false, sub_zero]
  · simp only [if_neg (not_le_of_gt ha), if_neg (not_lt_of_ge ha.le),
      if_neg ha.ne', sub_self]

/-- The lifetime-step left limit uses the strict event, at every finite time including zero. -/
theorem leftLimitProcess_indicator_lifetime_le (τ : Ω → WithTop ℝ≥0) (Z : Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    leftLimitProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω =
      {v | τ v < (t : WithTop ℝ≥0)}.indicator Z ω := by
  classical
  cases hτ : τ ω with
  | top =>
    have hc : Function.leftLim (fun _ : ℝ≥0 ↦ (0 : ℝ)) t = 0 :=
      (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))).continuousWithinAt.leftLim_eq
    simp only [leftLimitProcess, indicator_apply, mem_ofPred_eq, hτ,
      WithTop.not_top_le_coe, not_top_lt, if_false, hc, ite_self]
  | coe a =>
    simpa only [leftLimitProcess, indicator_apply, mem_ofPred_eq, hτ,
      WithTop.coe_le_coe, WithTop.coe_lt_coe] using leftLimitProcess_step_Ici a Z t ω

/-- The exact jump of a lifetime step is its coefficient on the finite lifetime graph.
At zero the jump retains the initial coefficient when the lifetime is zero. -/
theorem jumpProcess_indicator_lifetime_le (τ : Ω → WithTop ℝ≥0) (Z : Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    jumpProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω =
      {v | τ v = (t : WithTop ℝ≥0)}.indicator Z ω := by
  classical
  change {v | τ v ≤ (t : WithTop ℝ≥0)}.indicator Z ω -
    leftLimitProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω = _
  rw [leftLimitProcess_indicator_lifetime_le]
  simp only [indicator_apply, mem_ofPred_eq]
  rcases lt_trichotomy (τ ω) (t : WithTop ℝ≥0) with ht | ht | ht
  · simp only [if_pos ht.le, if_pos ht, if_neg ht.ne, sub_self]
  · simp only [ht, le_refl, if_true, lt_self_iff_false, if_false, sub_zero]
  · simp only [if_neg (not_le_of_gt ht), if_neg (not_lt_of_ge ht.le),
      if_neg ht.ne', sub_self]

/-- An infinite lifetime contributes no left value at any finite time. -/
theorem leftLimitProcess_indicator_lifetime_le_of_eq_top
    {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ} {ω : Ω} (hτ : τ ω = ⊤) (t : ℝ≥0) :
    leftLimitProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω = 0 := by
  classical
  rw [leftLimitProcess_indicator_lifetime_le]
  simp only [indicator_apply, mem_ofPred_eq, hτ, not_top_lt, if_false]

/-- An infinite lifetime contributes no finite-time jump. -/
theorem jumpProcess_indicator_lifetime_le_of_eq_top
    {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ} {ω : Ω} (hτ : τ ω = ⊤) (t : ℝ≥0) :
    jumpProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω = 0 := by
  classical
  rw [jumpProcess_indicator_lifetime_le]
  simp only [indicator_apply, mem_ofPred_eq, hτ, WithTop.top_ne_coe, if_false]

/-- A lifetime-zero step has left value zero at zero and its coefficient at every positive time. -/
theorem leftLimitProcess_indicator_lifetime_le_of_eq_zero
    {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ} {ω : Ω} (hτ : τ ω = 0) (t : ℝ≥0) :
    leftLimitProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω =
      if t = 0 then 0 else Z ω := by
  classical
  rw [leftLimitProcess_indicator_lifetime_le]
  simp only [indicator_apply, mem_ofPred_eq, hτ, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  by_cases ht : t = 0
  · subst t
    simp only [lt_self_iff_false, if_false, if_true]
  · rw [if_pos (pos_iff_ne_zero.mpr ht), if_neg ht]

/-- A lifetime-zero step retains its coefficient as the initial jump,
not as a positive-time jump. -/
theorem jumpProcess_indicator_lifetime_le_of_eq_zero
    {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ} {ω : Ω} (hτ : τ ω = 0) (t : ℝ≥0) :
    jumpProcess (fun s v ↦ {v | τ v ≤ (s : WithTop ℝ≥0)}.indicator Z v) t ω =
      if t = 0 then Z ω else 0 := by
  classical
  rw [jumpProcess_indicator_lifetime_le]
  simp only [indicator_apply, mem_ofPred_eq, hτ, ← WithTop.coe_zero,
    WithTop.coe_eq_coe, eq_comm]

/-- Finite sums of lifetime steps have the sum of the strict-event coefficients as their left
limit. The formula remains valid at zero and allows repeated or infinite lifetimes. -/
theorem leftLimitProcess_finset_sum_indicator_lifetime_le {ι : Type*} (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    leftLimitProcess
      (fun u v ↦ ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω =
      ∑ i ∈ s, {v | τ i v < (t : WithTop ℝ≥0)}.indicator (Z i) ω := by
  classical
  by_cases ht : t = 0
  · subst t
    rw [leftLimitProcess_zero]
    change 0 = _
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [indicator_of_notMem]
    change ¬ τ i ω < ((0 : ℝ≥0) : WithTop ℝ≥0)
    exact not_lt_of_ge bot_le
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [leftLimitProcess, if_neg ht]
    apply leftLim_eq_of_tendsto
    apply tendsto_finsetSum s
    intro i _
    have hi := (isCadlagPath_indicator_lifetime_le (τ i) (Z i) ω).tendsto_leftLimitProcess ht
    simpa only [leftLimitProcess_indicator_lifetime_le] using hi

/-- A finite collection of lifetime steps contributes exactly the sum of the coefficients of
the steps that jump at the current time. Coincident jumps are deliberately added. -/
theorem jumpProcess_finset_sum_indicator_lifetime_le {ι : Type*} (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    jumpProcess
      (fun u v ↦ ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω =
      ∑ i ∈ s, {v | τ i v = (t : WithTop ℝ≥0)}.indicator (Z i) ω := by
  change (∑ i ∈ s, {v | τ i v ≤ (t : WithTop ℝ≥0)}.indicator (Z i) ω) -
    leftLimitProcess
      (fun u v ↦ ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω = _
  rw [leftLimitProcess_finset_sum_indicator_lifetime_le, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := jumpProcess_indicator_lifetime_le (τ i) (Z i) t ω
  simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess_indicator_lifetime_le] using hi

end ProbabilityTheory
