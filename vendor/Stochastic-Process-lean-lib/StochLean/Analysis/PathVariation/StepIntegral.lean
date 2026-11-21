/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import Mathlib.Tactic.Order

/-!
# Representation independence of finite interval integration

The integrator is an arbitrary real-valued function. A zero finite linear
combination of half-open interval indicators has zero increment integral.
This is the deterministic algebra behind Protter's elementary integral.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology BigOperators

namespace StochLean

private theorem intervalStep_eventually_right (a b s : ℝ≥0) (c : ℝ) :
    ∀ᶠ t in nhdsWithin s (Ioi s),
      (if a < t ∧ t ≤ b then c else 0) = (if a ≤ s ∧ s < b then c else 0) := by
  by_cases ha : a ≤ s
  · by_cases hb : s < b
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
      simp [ha, hb, ha.trans_lt ht, htb.le]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hbt : b < t := (le_of_not_gt hb).trans_lt ht
      simp [hb, not_le_of_gt hbt]
  · filter_upwards [(eventually_lt_nhds (lt_of_not_ge ha)).filter_mono nhdsWithin_le_nhds]
      with t ht
    simp [ha, not_lt_of_ge ht.le]

/-- A zero interval step function integrates to zero against every integrator. -/
theorem sum_intervalIncrement_eq_zero {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (hzero : ∀ t : ℝ≥0, 0 < t → ∑ i, (if a i < t ∧ t ≤ b i then c i else 0) = 0)
    (f : ℝ≥0 → ℝ) : ∑ i, c i * (f (b i) - f (a i)) = 0 := by
  classical
  have hright (s : ℝ≥0) : ∑ i, (if a i ≤ s ∧ s < b i then c i else 0) = 0 := by
    have hinterval := Filter.eventually_all.mpr fun i ↦
      intervalStep_eventually_right (a i) (b i) s (c i)
    have hpos : ∀ᶠ t in nhdsWithin s (Ioi s), s < t := self_mem_nhdsWithin
    obtain ⟨t, ht, heq⟩ := (hpos.and hinterval).exists
    have hsum := hzero t (lt_of_le_of_lt bot_le ht)
    simpa only [heq] using hsum
  have hpoint (s : ℝ≥0) : ∑ i, (if a i < s ∧ s ≤ b i then c i else 0) = 0 := by
    by_cases hs : s = 0
    · subst s
      simp
    · exact hzero s (lt_of_le_of_ne bot_le (Ne.symm hs))
  have hmass (s : ℝ≥0) :
      (∑ i, if b i = s then c i else 0) - (∑ i, if a i = s then c i else 0) = 0 := by
    have hcell (i : ι) :
        (if b i = s then c i else 0) - (if a i = s then c i else 0) =
          (if a i < s ∧ s ≤ b i then c i else 0) -
            (if a i ≤ s ∧ s < b i then c i else 0) := by
      have hi := hab i
      split_ifs <;> simp_all <;> grind
    rw [← sum_sub_distrib]
    simp_rw [hcell, sum_sub_distrib, hpoint, hright, sub_self]
  let S : Finset ℝ≥0 := univ.image a ∪ univ.image b
  have haS (i : ι) : a i ∈ S := mem_union_left _ (mem_image_of_mem a (mem_univ i))
  have hbS (i : ι) : b i ∈ S := mem_union_right _ (mem_image_of_mem b (mem_univ i))
  calc
    ∑ i, c i * (f (b i) - f (a i)) =
        ∑ i, ∑ s ∈ S, f s * ((if b i = s then c i else 0) -
          (if a i = s then c i else 0)) := by
      apply sum_congr rfl
      intro i _
      simp only [mul_sub, sum_sub_distrib, mul_ite, mul_zero]
      rw [sum_ite_eq S (b i), sum_ite_eq S (a i)]
      simp only [hbS, haS, ↓reduceIte]
      ring
    _ = ∑ s ∈ S, f s * ((∑ i, if b i = s then c i else 0) -
        (∑ i, if a i = s then c i else 0)) := by
      rw [sum_comm]
      simp only [mul_sum, mul_sub, sum_sub_distrib]
    _ = 0 := by simp only [hmass, mul_zero, sum_const_zero]

/-- Two interval representations of the same step function have equal increment integrals. -/
theorem sum_intervalIncrement_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (a' b' : κ → ℝ≥0) (c' : κ → ℝ)
    (hab : ∀ i, a i ≤ b i) (hab' : ∀ j, a' j ≤ b' j)
    (heq : ∀ t : ℝ≥0, 0 < t →
      (∑ i, if a i < t ∧ t ≤ b i then c i else 0) =
        ∑ j, if a' j < t ∧ t ≤ b' j then c' j else 0)
    (f : ℝ≥0 → ℝ) :
    (∑ i, c i * (f (b i) - f (a i))) = ∑ j, c' j * (f (b' j) - f (a' j)) := by
  classical
  have hz := sum_intervalIncrement_eq_zero
    (Sum.elim a a') (Sum.elim b b') (Sum.elim c (fun j ↦ -c' j))
    (fun i ↦ by cases i with | inl i => exact hab i | inr j => exact hab' j)
    (fun t ht ↦ by
      rw [Fintype.sum_sum_type]
      change (∑ i, if a i < t ∧ t ≤ b i then c i else 0) +
        (∑ j, if a' j < t ∧ t ≤ b' j then -c' j else 0) = 0
      have hneg (j : κ) : (if a' j < t ∧ t ≤ b' j then -c' j else 0) =
          -(if a' j < t ∧ t ≤ b' j then c' j else 0) := by
        split_ifs <;> simp
      simp only [hneg, sum_neg_distrib]
      rw [heq t ht, add_neg_cancel]) f
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib,
    add_neg_eq_zero] using hz

end StochLean
