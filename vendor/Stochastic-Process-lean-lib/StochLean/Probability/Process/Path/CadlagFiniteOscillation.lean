/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagBounded
public import StochLean.Probability.Process.Path.LeftLimit
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Small cadlag oscillations away from finitely many separating times

Compactness turns the two one-sided local limits into a finite collection
of separating points and one common distance scale. The points need not
be jumps; the assertion covers every sufficiently short interval which
does not cross any of them.
-/

@[expose] public section

open Set Filter Metric
open scoped NNReal Topology

namespace ProbabilityTheory

theorem IsCadlagPath.exists_same_side_oscillation_neighborhood
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (t : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set ℝ≥0, U ∈ 𝓝 t ∧ ∀ a ∈ U, ∀ b ∈ U,
      ((a < t ∧ b < t) ∨ (t ≤ a ∧ t ≤ b)) → dist (x a) (x b) < ε := by
  let U : Set ℝ≥0 := {s | if s < t then dist (x s) (Function.leftLim x t) < ε / 2
    else dist (x s) (x t) < ε / 2}
  have hU : U ∈ 𝓝 t := by
    rw [← nhdsLT_sup_nhdsGE t, Filter.mem_sup]
    constructor
    · by_cases ht : t = 0
      · subst t
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact ((not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ s)) hs).elim
      · have hl := (tendsto_leftLim_of_tendsto (hx.2 t ht)).eventually
          (Metric.ball_mem_nhds _ (half_pos hε))
        filter_upwards [hl, self_mem_nhdsWithin] with s hs hst
        simpa only [U, mem_ofPred_eq, if_pos (show s < t from hst), mem_ball] using hs
    · have hr := (hx.1 t).tendsto.eventually (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [hr, self_mem_nhdsWithin] with s hs hst
      simpa only [U, mem_ofPred_eq, if_neg (not_lt_of_ge (show t ≤ s from hst)), mem_ball]
        using hs
  refine ⟨U, hU, fun a ha b hb hab ↦ ?_⟩
  rcases hab with ⟨hat, hbt⟩ | ⟨hta, htb⟩
  · have ha' : dist (x a) (Function.leftLim x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_pos hat] using ha
    have hb' : dist (x b) (Function.leftLim x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_pos hbt] using hb
    have h := dist_triangle_right (x a) (x b) (Function.leftLim x t)
    linarith only [h, ha', hb']
  · have ha' : dist (x a) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg (not_lt_of_ge hta)] using ha
    have hb' : dist (x b) (x t) < ε / 2 := by
      simpa only [U, mem_ofPred_eq, if_neg (not_lt_of_ge htb)] using hb
    have h := dist_triangle_right (x a) (x b) (x t)
    linarith only [h, ha', hb']

theorem IsCadlagPath.exists_finite_separators_oscillation
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset ℝ≥0, (↑A : Set ℝ≥0) ⊆ Icc 0 T ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → dist a b < δ →
        (∀ s ∈ A, s ∉ Ioc a b) → dist (x a) (x b) < ε := by
  classical
  choose U hU hosc using fun t ↦ hx.exists_same_side_oscillation_neighborhood t hε
  obtain ⟨A, hA, hcover⟩ := (isCompact_Icc : IsCompact (Icc 0 T)).elim_nhds_subcover
    (fun t ↦ interior (U t)) (fun t _ ↦ interior_mem_nhds.mpr (hU t))
  have hcov : Icc 0 T ⊆ ⋃ s : (↑A : Set ℝ≥0), interior (U s) := by
    intro a ha
    obtain ⟨s, hs, has⟩ := mem_iUnion₂.mp (hcover ha)
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, has⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun _ : (↑A : Set ℝ≥0) ↦ isOpen_interior) hcov
  refine ⟨A, fun s hs ↦ hA s hs, δ, hδ, fun a ha b _ hab hd havoid ↦ ?_⟩
  obtain ⟨s, hs⟩ := hball a ha
  have hau : a ∈ U s := interior_subset (hs (mem_ball_self hδ))
  have hbu : b ∈ U s := interior_subset (hs (by simpa only [mem_ball, dist_comm] using hd))
  apply hosc s a hau b hbu
  by_cases has : a < s
  · exact Or.inl ⟨has, lt_of_not_ge (fun hsb ↦ havoid s s.2 ⟨has, hsb⟩)⟩
  · exact Or.inr ⟨le_of_not_gt has, (le_of_not_gt has).trans hab⟩

end ProbabilityTheory
