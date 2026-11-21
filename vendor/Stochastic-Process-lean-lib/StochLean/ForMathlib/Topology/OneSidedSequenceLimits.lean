/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Order.MonotoneSelection
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Analysis.Normed.Group.Real

/-! # One-sided limits from convergence of all monotone samples

Two distinct persistent levels would give one decreasing sequence whose even
and odd values remain separated. Convergence of every such sample rules this
out; local boundedness then supplies the actual filter limit. The theorem
works on an arbitrary subset, not only a dense subset.
-/

@[expose] public section

open Filter Set
open scoped Topology

theorem exists_limit_nhdsWithin_Ioi_of_antitone_limits
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {D : Set α} {f : α → ℝ} {t B : α} {C : ℝ} (hB : t < B)
    (hb : ∀ x ∈ D, t < x → x < B → ‖f x‖ ≤ C)
    (hlim : ∀ u : ℕ → α, Antitone u →
      (∀ n, t < u n ∧ u n < B ∧ u n ∈ D) →
      ∃ z : ℝ, Tendsto (fun n ↦ f (u n)) atTop (𝓝 z)) :
    ∃ z : ℝ, Tendsto f (nhdsWithin t (D ∩ Ioi t)) (𝓝 z) := by
  let L := nhdsWithin t (D ∩ Ioi t)
  have hev (y : α) (hy : t < y) : ∀ᶠ x in L, x ∈ D ∧ t < x ∧ x < y := by
    filter_upwards [self_mem_nhdsWithin (a := t) (s := D ∩ Ioi t),
      nhdsWithin_le_nhds (Iio_mem_nhds hy)] with x hx hxy
    exact ⟨hx.1, hx.2, hxy⟩
  have hnorm : ∀ᶠ x in L, ‖f x‖ ≤ C := (hev B hB).mono fun x hx ↦ hb x hx.1 hx.2.1 hx.2.2
  refine tendsto_of_no_upcrossings dense_univ ?_
    (isBoundedUnder_of_eventually_le (hnorm.mono fun x hx ↦ (le_abs_self _).trans hx))
    (isBoundedUnder_of_eventually_ge
      (hnorm.mono fun x hx ↦ (neg_le_neg hx).trans (neg_abs_le _)))
  rintro a _ b _ hab ⟨hl, hu⟩
  have hlow (y : α) (hy : t < y) : ∃ x, t < x ∧ x < y ∧ x ∈ D ∧ f x < a := by
    obtain ⟨x, hx, hD, htx, hxy⟩ := (hl.and_eventually (hev y hy)).exists
    exact ⟨x, htx, hxy, hD, hx⟩
  have hhigh (y : α) (hy : t < y) : ∃ x, t < x ∧ x < y ∧ x ∈ D ∧ b < f x := by
    obtain ⟨x, hx, hD, htx, hxy⟩ := (hu.and_eventually (hev y hy)).exists
    exact ⟨x, htx, hxy, hD, hx⟩
  let p (n : ℕ) (x : α) := x ∈ D ∧ if n % 2 = 0 then f x < a else b < f x
  have hp (n : ℕ) (y : α) (hy : t < y) : ∃ x, t < x ∧ x < y ∧ p n x := by
    by_cases hn : n % 2 = 0
    · simpa only [p, hn, if_true] using hlow y hy
    · simpa only [p, hn, if_false] using hhigh y hy
  obtain ⟨u, hanti, hmem⟩ := exists_strictAnti_seq_of_between hB hp
  obtain ⟨z, hz⟩ := hlim u hanti.antitone (fun n ↦
    ⟨(hmem n).1, (hmem n).2.1, (hmem n).2.2.1⟩)
  have hflo : ∃ᶠ n : ℕ in atTop, f (u n) ≤ a := by
    rw [frequently_atTop]
    intro N
    refine ⟨2 * N, by omega, ?_⟩
    have hv := (hmem (2 * N)).2.2.2
    have he : 2 * N % 2 = 0 := by omega
    exact (by simpa only [he, if_true] using hv : f (u (2 * N)) < a).le
  have hfhi : ∃ᶠ n : ℕ in atTop, b ≤ f (u n) := by
    rw [frequently_atTop]
    intro N
    refine ⟨2 * N + 1, by omega, ?_⟩
    have hv := (hmem (2 * N + 1)).2.2.2
    have he : (2 * N + 1) % 2 ≠ 0 := by omega
    exact (by simpa only [he, if_false] using hv : b < f (u (2 * N + 1))).le
  exact (not_le_of_gt hab)
    ((ge_of_tendsto_of_frequently hz hfhi).trans (le_of_tendsto_of_frequently hz hflo))

theorem exists_limit_nhdsWithin_Iio_of_monotone_limits
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {D : Set α} {f : α → ℝ} {B t : α} {C : ℝ} (hB : B < t)
    (hb : ∀ x ∈ D, x < t → B < x → ‖f x‖ ≤ C)
    (hlim : ∀ u : ℕ → α, Monotone u →
      (∀ n, u n < t ∧ B < u n ∧ u n ∈ D) →
      ∃ z : ℝ, Tendsto (fun n ↦ f (u n)) atTop (𝓝 z)) :
    ∃ z : ℝ, Tendsto f (nhdsWithin t (D ∩ Iio t)) (𝓝 z) :=
  exists_limit_nhdsWithin_Ioi_of_antitone_limits (α := αᵒᵈ) hB hb hlim
