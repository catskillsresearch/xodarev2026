/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CellInsertion
public import StochLean.Analysis.PathVariation.TaggedStepApproximation
public import StochLean.Analysis.PathVariation.CommonRefinement
public import StochLean.Analysis.PathVariation.EndpointInvariance

/-! # Fixed finite insertions preserve a continuous-path QV limit

A newly inserted point lies between two endpoints converging to that point.
The exact product error therefore vanishes. Finite iteration preserves all old
endpoints and the mesh bound, without any finite-variation assumption on the path.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace StochLean

theorem exists_insertPoint_preserving_quadraticVariation {T : ℝ≥0}
    {π : ℕ → TimePartition T} {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T))
    (hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {q : ℝ} (hQ : HasQuadraticVariationAlong π x q) {s : ℝ≥0} (hs : s ∈ Icc 0 T) :
    ∃ ρ : ℕ → TimePartition T, (∀ n, (ρ n).Refines (π n)) ∧
      (∀ n, Set.range (ρ n).point = insert s (Set.range (π n).point)) ∧
      HasQuadraticVariationAlong ρ x q := by
  by_cases hz : s = 0
  · subst s
    refine ⟨π, fun _ _ h ↦ h, fun n ↦ ?_, hQ⟩
    have hmem : (0 : ℝ≥0) ∈ Set.range (π n).point := ⟨0, (π n).first_eq_zero⟩
    exact (Set.insert_eq_of_mem hmem).symm
  have hi (n : ℕ) : ∃ i : Fin (π n).size, (π n).left i < s ∧ s ≤ (π n).right i :=
    (π n).exists_cell ⟨pos_iff_ne_zero.mpr hz, hs.2⟩
  choose i hi using hi
  have hl : Tendsto (fun n ↦ (π n).left (i n)) atTop (𝓝 s) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hm.eventually_lt_const hε] with n hn
    rw [dist_comm]
    exact ((π n).dist_left_of_mem_cell_le_mesh (hi n)).trans_lt hn
  have hr : Tendsto (fun n ↦ (π n).right (i n)) atTop (𝓝 s) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hm.eventually_lt_const hε] with n hn
    rw [dist_comm]
    exact ((π n).dist_tag_of_mem_cell_le_mesh (π n).right
      (fun j ↦ ⟨(π n).left_le_right j, le_rfl⟩) (hi n)).trans_lt hn
  have hxl : Tendsto (fun n ↦ x ((π n).left (i n))) atTop (𝓝 (x s)) :=
    (hx s hs).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hl,
      Eventually.of_forall fun n ↦ ⟨bot_le, (π n).point_le_horizon _⟩⟩)
  have hxr : Tendsto (fun n ↦ x ((π n).right (i n))) atTop (𝓝 (x s)) :=
    (hx s hs).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hr,
      Eventually.of_forall fun n ↦ ⟨bot_le, (π n).point_le_horizon _⟩⟩)
  choose ρ href hpoints he using fun n ↦
    (π n).exists_insertPoint_in_cell (i n) ⟨(hi n).1.le, (hi n).2⟩ x
  refine ⟨ρ, href, hpoints, ?_⟩
  have herr : Tendsto (fun n ↦ 2 * (x s - x ((π n).left (i n))) *
      (x ((π n).right (i n)) - x s)) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero, zero_mul] using
      (((tendsto_const_nhds (x := x s)).sub hxl).const_mul 2).mul (hxr.sub_const (x s))
  simpa only [HasQuadraticVariationAlong, sub_zero] using
    (hQ.sub herr).congr (fun n ↦ (he n).symm)

theorem exists_finiteInsertion_preserving_quadraticVariation {T : ℝ≥0}
    {π : ℕ → TimePartition T} {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T))
    (hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {q : ℝ} (hQ : HasQuadraticVariationAlong π x q)
    (s : Finset ℝ≥0) (hs : ∀ t ∈ s, t ≤ T) :
    ∃ ρ : ℕ → TimePartition T, (∀ n, (ρ n).Refines (π n)) ∧
      (∀ n, Set.range (ρ n).point = (s : Set ℝ≥0) ∪ Set.range (π n).point) ∧
      HasQuadraticVariationAlong ρ x q := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨π, fun _ _ h ↦ h, fun _ ↦ by simp, hQ⟩
  | @insert t s ht ih =>
    intro hs
    obtain ⟨ρ, href, hpoints, hq⟩ := ih (fun u hu ↦ hs u (Finset.mem_insert_of_mem hu))
    have hmρ : Tendsto (fun n ↦ ((ρ n).mesh : ℝ)) atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ NNReal.coe_nonneg _)
        (fun n ↦ by exact_mod_cast (href n).mesh_le) hm
    obtain ⟨σ, hσ, hσpoints, hσq⟩ := exists_insertPoint_preserving_quadraticVariation hx hmρ hq
      ⟨bot_le, hs t (Finset.mem_insert_self _ _)⟩
    refine ⟨σ, fun n _ h ↦ hσ n (href n h), fun n ↦ ?_, hσq⟩
    rw [hσpoints, hpoints]
    simp only [Finset.coe_insert, Set.insert_union]

theorem hasQuadraticVariationAlong_commonRefinement {T : ℝ≥0}
    {π : ℕ → TimePartition T} {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T))
    (hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {q : ℝ} (hQ : HasQuadraticVariationAlong π x q) (σ : TimePartition T) :
    HasQuadraticVariationAlong (fun n ↦ (π n).commonRefinement σ) x q := by
  classical
  obtain ⟨ρ, _, hpoints, hq⟩ := exists_finiteInsertion_preserving_quadraticVariation hx hm hQ
    (Finset.univ.image σ.point) (by
      intro t ht
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      exact σ.point_le_horizon i)
  apply hq.congr
  intro n
  apply quadraticVariationSum_eq_of_range_eq
  rw [hpoints, TimePartition.commonRefinement_range]
  simp [Set.union_comm]

end StochLean
