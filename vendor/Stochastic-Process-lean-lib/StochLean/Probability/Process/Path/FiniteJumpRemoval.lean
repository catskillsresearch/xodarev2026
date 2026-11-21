/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LifetimeStepJump

/-! # Finite jump removal with bounded residual estimates

Only a fixed finite family of lifetime steps is removed. Its coefficients need not have
an integrable random jump count. A pathwise truncation by the original increment bound
is made before any conditional expectation is taken; no interchange of `min` and
conditional expectation is asserted.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

theorem indicator_lifetime_le_sub_eq_window (τ : Ω → WithTop ℝ≥0) (Z : Ω → ℝ)
    {t u : ℝ≥0} (htu : t ≤ u) (ω : Ω) :
    {v | τ v ≤ (u : WithTop ℝ≥0)}.indicator Z ω -
      {v | τ v ≤ (t : WithTop ℝ≥0)}.indicator Z ω =
        {v | (t : WithTop ℝ≥0) < τ v ∧ τ v ≤ (u : WithTop ℝ≥0)}.indicator Z ω := by
  classical
  simp only [indicator_apply, mem_ofPred_eq]
  by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
  · have hu := ht.trans (WithTop.coe_le_coe.mpr htu)
    simp only [ht, hu, not_lt_of_ge ht, false_and, if_true, if_false, sub_self]
  · simp only [ht, lt_of_not_ge ht, true_and, if_false, sub_zero]

theorem norm_finset_lifetime_step_increment_le (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) {t u : ℝ≥0} (htu : t ≤ u)
    (ω : Ω) {C : ℝ} (hZ : ∀ i ∈ s, ‖Z i ω‖ ≤ C) :
    ‖(∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) ω) -
      (∑ i ∈ s, {v | τ i v ≤ (t : WithTop ℝ≥0)}.indicator (Z i) ω)‖ ≤
        C * ∑ i ∈ s, {v | (t : WithTop ℝ≥0) < τ i v ∧
          τ i v ≤ (u : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  classical
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [indicator_lifetime_le_sub_eq_window (τ i) (Z i) htu ω]
  by_cases hw : (t : WithTop ℝ≥0) < τ i ω ∧ τ i ω ≤ (u : WithTop ℝ≥0)
  · simpa only [indicator_apply, mem_ofPred_eq, if_pos hw, mul_one] using hZ i hi
  · simp only [indicator_apply, mem_ofPred_eq, if_neg hw, norm_zero, mul_zero, le_refl]

/-- Finite removal produces a cadlag residual, with arbitrary repeated/infinite
lifetimes and arbitrary coefficients. No stopping or measurability assertion is needed. -/
theorem IsCadlagPath.sub_finset_lifetime_steps {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : IsCadlagPath (X · ω)) (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) :
    IsCadlagPath (fun t ↦ X t ω -
      ∑ i ∈ s, {v | τ i v ≤ (t : WithTop ℝ≥0)}.indicator (Z i) ω) :=
  hX.sub (IsCadlagPath.finset_sum s _
    (fun i _ ↦ isCadlagPath_indicator_lifetime_le (τ i) (Z i) ω))

/-- The clipped residual estimate is pathwise. Taking conditional expectations
after this inequality is safe even when the total number of jumps has no moment. -/
theorem norm_increment_le_clipped_residual_add_windows (X : ℝ≥0 → Ω → ℝ)
    (s : Finset ι) (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ)
    {t u : ℝ≥0} (htu : t ≤ u) (ω : Ω) {N : ℝ}
    (ht : ‖X t ω‖ ≤ N) (hu : ‖X u ω‖ ≤ N) (hZ : ∀ i ∈ s, ‖Z i ω‖ ≤ 2 * N) :
    let J : ℝ≥0 → ℝ := fun r ↦
      ∑ i ∈ s, {v | τ i v ≤ (r : WithTop ℝ≥0)}.indicator (Z i) ω
    ‖X u ω - X t ω‖ ≤ min (2 * N) ‖(X u ω - J u) - (X t ω - J t)‖ +
      2 * N * ∑ i ∈ s, {v | (t : WithTop ℝ≥0) < τ i v ∧
        τ i v ≤ (u : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  intro J
  let A := ∑ i ∈ s, {v | (t : WithTop ℝ≥0) < τ i v ∧
    τ i v ≤ (u : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω
  have hN : 0 ≤ N := (norm_nonneg _).trans ht
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hbound : ‖X u ω - X t ω‖ ≤ 2 * N :=
    (norm_sub_le _ _).trans (by linarith)
  have hstep : ‖J u - J t‖ ≤ 2 * N * A :=
    norm_finset_lifetime_step_increment_le s τ Z htu ω hZ
  have he : X u ω - X t ω = ((X u ω - J u) - (X t ω - J t)) + (J u - J t) := by ring
  have hres : ‖X u ω - X t ω‖ ≤ ‖(X u ω - J u) - (X t ω - J t)‖ + 2 * N * A := by
    calc
      _ = ‖((X u ω - J u) - (X t ω - J t)) + (J u - J t)‖ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl hstep)
  change _ ≤ min _ _ + 2 * N * A
  by_cases hsmall : ‖(X u ω - J u) - (X t ω - J t)‖ ≤ 2 * N
  · rw [min_eq_right hsmall]
    exact hres
  · rw [min_eq_left (le_of_not_ge hsmall)]
    exact hbound.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hA))

/-- Removing an actual jump once cancels it exactly. Finite lifetimes must be
distinct at the time under consideration; repeated infinite lifetimes are allowed. -/
theorem IsCadlagPath.jump_sub_finset_lifetime_steps_of_mem
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    (s : Finset ι) (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ)
    {i : ι} (hi : i ∈ s) {t : ℝ≥0} (hit : τ i ω = (t : WithTop ℝ≥0))
    (hZi : Z i ω = jumpProcess X t ω)
    (huniq : ∀ j ∈ s, τ j ω = (t : WithTop ℝ≥0) → j = i) :
    jumpProcess (fun u v ↦ X u v -
      ∑ j ∈ s, {v | τ j v ≤ (u : WithTop ℝ≥0)}.indicator (Z j) v) t ω = 0 := by
  classical
  let J : ℝ≥0 → Ω → ℝ := fun u v ↦
    ∑ j ∈ s, {v | τ j v ≤ (u : WithTop ℝ≥0)}.indicator (Z j) v
  have hcJ : IsCadlagPath (J · ω) := IsCadlagPath.finset_sum s _
    (fun j _ ↦ isCadlagPath_indicator_lifetime_le (τ j) (Z j) ω)
  change jumpProcess (X - J) t ω = 0
  rw [hX.jumpProcess_sub hcJ t]
  have he : jumpProcess J t ω = Z i ω := by
    rw [show jumpProcess J t ω = _ from
      jumpProcess_finset_sum_indicator_lifetime_le s τ Z t ω]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem (s := {v | τ i v = (t : WithTop ℝ≥0)}) hit _
    · intro j hj hji
      exact indicator_of_notMem (s := {v | τ j v = (t : WithTop ℝ≥0)})
        (fun hjt ↦ hji (huniq j hj hjt)) _
    · exact fun hnot ↦ (hnot hi).elim
  rw [he, hZi, sub_self]

/-- Away from all selected lifetimes the residual keeps the original jump. -/
theorem IsCadlagPath.jump_sub_finset_lifetime_steps_of_not_mem
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    (s : Finset ι) (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ)
    (t : ℝ≥0) (ht : ∀ i ∈ s, τ i ω ≠ (t : WithTop ℝ≥0)) :
    jumpProcess (fun u v ↦ X u v -
      ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω =
        jumpProcess X t ω := by
  classical
  let J : ℝ≥0 → Ω → ℝ := fun u v ↦
    ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v
  have hcJ : IsCadlagPath (J · ω) := IsCadlagPath.finset_sum s _
    (fun i _ ↦ isCadlagPath_indicator_lifetime_le (τ i) (Z i) ω)
  change jumpProcess (X - J) t ω = _
  rw [hX.jumpProcess_sub hcJ t]
  have he : jumpProcess J t ω = 0 := by
    rw [show jumpProcess J t ω = _ from
      jumpProcess_finset_sum_indicator_lifetime_le s τ Z t ω]
    exact Finset.sum_eq_zero fun i hi ↦
      indicator_of_notMem (s := {v | τ i v = (t : WithTop ℝ≥0)}) (ht i hi) _
  rw [he, sub_zero]

/-- If a finite list covers every large jump and removes each selected jump
exactly once, then every positive-time jump of the residual is small. -/
theorem IsCadlagPath.norm_jump_sub_finset_lifetime_steps_le
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    (s : Finset ι) (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ)
    (T : ℝ≥0) {b : ℝ} (hb : 0 ≤ b)
    (hZ : ∀ i ∈ s, ∀ t : ℝ≥0, τ i ω = (t : WithTop ℝ≥0) → Z i ω = jumpProcess X t ω)
    (huniq : ∀ i ∈ s, ∀ j ∈ s, ∀ t : ℝ≥0,
      τ i ω = (t : WithTop ℝ≥0) → τ j ω = (t : WithTop ℝ≥0) → i = j)
    (hcover : ∀ t : ℝ≥0, 0 < t → t ≤ T → b < ‖jumpProcess X t ω‖ →
      ∃ i ∈ s, τ i ω = (t : WithTop ℝ≥0)) :
    ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ‖jumpProcess (fun u v ↦ X u v -
        ∑ i ∈ s, {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) v) t ω‖ ≤ b := by
  intro t ht htT
  by_cases hmem : ∃ i ∈ s, τ i ω = (t : WithTop ℝ≥0)
  · obtain ⟨i, hi, hit⟩ := hmem
    rw [hX.jump_sub_finset_lifetime_steps_of_mem s τ Z hi hit (hZ i hi t hit)
      (fun j hj hjt ↦ huniq j hj i hi t hjt hit), norm_zero]
    exact hb
  · rw [hX.jump_sub_finset_lifetime_steps_of_not_mem s τ Z t
      (fun i hi hit ↦ hmem ⟨i, hi, hit⟩)]
    exact le_of_not_gt (fun hj ↦ hmem (hcover t ht htT hj))

end ProbabilityTheory
