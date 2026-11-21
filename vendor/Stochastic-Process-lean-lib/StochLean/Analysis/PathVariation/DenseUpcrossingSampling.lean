/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.DenseUpcrossings
public import StochLean.ForMathlib.Probability.UpcrossingCongruence
public import StochLean.ForMathlib.Probability.UpcrossingReversal
public import Mathlib.Probability.Martingale.Convergence

/-! # Monotone samples of the existing dyadic skeleton

Every finite sample prefix is contained in a common expanding grid. Its native
crossing count is bounded by the dense count. For decreasing samples, reversal
and negation preserve the count with the required extra terminal index.
These are deterministic statements about a single trajectory.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace StochLean

theorem TimePartition.upcrossingsBefore_sample_le
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {a b : ℝ} {T : ℝ≥0}
    (hab : a < b) (π : TimePartition T) {e : ℕ → ℝ≥0} (he : Monotone e) (N : ℕ)
    (hmem : ∀ k ≤ N, e k ∈ Set.range π.point) :
    upcrossingsBefore a b (fun k ↦ X (e k)) N ω ≤
      upcrossingsBefore a b (fun k ↦ X (π.pointNat k)) (π.size + 1) ω := by
  let j (k : ℕ) : ℕ := (π.ceilingIndex (e k)).val
  have hj : Monotone j := fun _ _ h ↦ π.ceilingIndex_mono (he h)
  have h := upcrossingsBefore_comp_le (f := fun k ↦ X (π.pointNat k))
    (ω := ω) (N := N) hab hj (fun k _ ↦ (π.ceilingIndex (e k)).isLt)
  have heq : upcrossingsBefore a b (fun k ↦ X (π.pointNat (j k))) N ω =
      upcrossingsBefore a b (fun k ↦ X (e k)) N ω := by
    apply upcrossingsBefore_congr_on_Iic
    intro k hk
    exact congrFun (congrArg X (π.pointNat_ceilingIndex_eq_of_mem (hmem k hk))) ω
  rwa [heq] at h

theorem exists_expandingDyadic_contains_prefix {e : ℕ → ℝ≥0}
    (he : ∀ k, ∃ m, e k ∈ Set.range (TimePartition.expandingDyadic m).point) (N : ℕ) :
    ∃ m, ∀ k ≤ N, e k ∈ Set.range (TimePartition.expandingDyadic m).point := by
  classical
  choose m hm using he
  refine ⟨(range (N + 1)).sup m, fun k hk ↦ ?_⟩
  exact TimePartition.expandingDyadic_range_mono
    (Finset.le_sup (mem_range.mpr (Nat.lt_succ_of_le hk))) (hm k)

theorem upcrossingsBefore_monotone_sample_le_dense
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {a b : ℝ} (hab : a < b)
    {e : ℕ → ℝ≥0} (he : Monotone e)
    (hmem : ∀ k, ∃ m, e k ∈ Set.range (TimePartition.expandingDyadic m).point) (N : ℕ) :
    (upcrossingsBefore a b (fun k ↦ X (e k)) N ω : ℝ≥0∞) ≤
      denseUpcrossings a b X ω := by
  obtain ⟨m, hm⟩ := exists_expandingDyadic_contains_prefix hmem N
  apply (Nat.cast_le.mpr ((TimePartition.expandingDyadic m).upcrossingsBefore_sample_le
    hab he N hm)).trans
  exact le_iSup (fun n ↦ (upcrossingsBefore a b
    (fun k ↦ X ((TimePartition.expandingDyadic n).pointNat k))
      ((TimePartition.expandingDyadic n).size + 1) ω : ℝ≥0∞)) m

theorem upcrossings_monotone_sample_le_dense
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {a b : ℝ} (hab : a < b)
    {e : ℕ → ℝ≥0} (he : Monotone e)
    (hmem : ∀ k, ∃ m, e k ∈ Set.range (TimePartition.expandingDyadic m).point) :
    upcrossings a b (fun k ↦ X (e k)) ω ≤ denseUpcrossings a b X ω :=
  iSup_le (upcrossingsBefore_monotone_sample_le_dense hab he hmem)

theorem upcrossings_antitone_sample_le_dense_neg
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {a b : ℝ} (hab : a < b)
    {e : ℕ → ℝ≥0} (he : Antitone e)
    (hmem : ∀ k, ∃ m, e k ∈ Set.range (TimePartition.expandingDyadic m).point) :
    upcrossings a b (fun k ↦ X (e k)) ω ≤
      denseUpcrossings (-b) (-a) (fun t ω ↦ -X t ω) ω := by
  apply iSup_le
  intro N
  have hm : Monotone (fun k ↦ e (N - k)) := fun _ _ h ↦ he (Nat.sub_le_sub_left h N)
  exact (Nat.cast_le.mpr (upcrossingsBefore_le_neg_reverse hab N ω)).trans
    (upcrossingsBefore_monotone_sample_le_dense (neg_lt_neg hab) hm
      (fun k ↦ hmem (N - k)) (N + 1))

private theorem exists_limit_of_bounded_upcrossings
    {Ω : Type*} {f : ℕ → Ω → ℝ} {ω : Ω}
    (hb : BddAbove (Set.range fun n ↦ ‖f n ω‖))
    (hu : ∀ a b : ℚ, a < b → upcrossings a b f ω < ⊤) :
    ∃ z : ℝ, Tendsto (fun n ↦ f n ω) atTop (𝓝 z) := by
  obtain ⟨C, hC⟩ := hb
  have hm (n) : ‖f n ω‖ ≤ C := hC (Set.mem_range_self n)
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    exact not_frequently_of_upcrossings_lt_top hab (hu a b (Rat.cast_lt.mp hab)).ne
  · exact isBoundedUnder_of ⟨C, fun n ↦ (le_abs_self _).trans (hm n)⟩
  · exact isBoundedUnder_of ⟨-C, fun n ↦ (neg_le_neg (hm n)).trans (neg_abs_le _)⟩

theorem exists_limit_monotone_dense_sample
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {e : ℕ → ℝ≥0} (he : Monotone e)
    (hmem : ∀ k, ∃ m, e k ∈ Set.range (TimePartition.expandingDyadic m).point)
    (hb : BddAbove (Set.range fun n ↦ ‖X (e n) ω‖))
    (hu : ∀ a b : ℚ, a < b → denseUpcrossings a b X ω < ⊤) :
    ∃ z : ℝ, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 z) := by
  apply exists_limit_of_bounded_upcrossings hb
  intro a b hab
  exact (upcrossings_monotone_sample_le_dense (Rat.cast_lt.mpr hab) he hmem).trans_lt
    (hu a b hab)

theorem exists_limit_antitone_dense_sample
    {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {e : ℕ → ℝ≥0} (he : Antitone e)
    (hmem : ∀ k, ∃ m, e k ∈ Set.range (TimePartition.expandingDyadic m).point)
    (hb : BddAbove (Set.range fun n ↦ ‖X (e n) ω‖))
    (hu : ∀ a b : ℚ, a < b → denseUpcrossings a b (fun t ω ↦ -X t ω) ω < ⊤) :
    ∃ z : ℝ, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 z) := by
  apply exists_limit_of_bounded_upcrossings hb
  intro a b hab
  have hh := hu (-b) (-a) (neg_lt_neg hab)
  simp only [Rat.cast_neg] at hh
  exact (upcrossings_antitone_sample_le_dense_neg (Rat.cast_lt.mpr hab) he hmem).trans_lt hh

end StochLean
