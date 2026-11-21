/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalCountSum

/-! # Stopping a count-minus-series at an actual arrival

Suppose each summand vanishes up to and including its birth time: zero for
the first summand, and the preceding actual arrival for subsequent ones.
Stopping the count-minus-series at arrival `m` is then exactly the stopped
sum of its first `m + 1` compensated indicators.

The finite stopped clock is established before conversion from extended
time. The term of index `m + 1` vanishes also at its birth endpoint, which
is essential for this precise prefix length. Summands need not themselves
be stopped processes. No measure, measurability, integrability, convergence
certificate or additional series owner is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- A count-minus-series whose terms vanish through their actual births
has an exact finite-prefix representation after stopping at arrival `m`. -/
theorem stoppedProcess_count_sub_tsum_eq_sum_range
    {Ω : Type*} {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (D : ℕ → ℝ≥0 → Ω → ℝ)
    (hzero : ∀ n : ℕ,
      let L : Ω → WithTop ℝ≥0 :=
        Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
      ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ L ω → D n t ω = 0)
    (m : ℕ) :
    stoppedProcess (fun t ω ↦ ((hΓ ω).count t : ℝ) - ∑' n : ℕ, D n t ω) (Γ m) =
      stoppedProcess (fun (t : ℝ≥0) (ω : Ω) ↦
        ∑ n ∈ Finset.range (m + 1),
          ((if Γ n ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) - D n t ω)) (Γ m) := by
  classical
  funext t ω
  let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (Γ m ω)).untopA
  have hfin : min (t : WithTop ℝ≥0) (Γ m ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hu : (u : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (Γ m ω) := by
    dsimp only [u]
    rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
  have hcount : (hΓ ω).count u ≤ m + 1 := by
    change (hΓ ω).count (min (t : WithTop ℝ≥0) (Γ m ω)).untopA ≤ m + 1
    rw [(hΓ ω).count_min_arrival m t]
    exact min_le_right _ _
  have hzero_tail (n : ℕ) (hn : n ∉ Finset.range (m + 1)) : D n u ω = 0 := by
    have hmn : m + 1 ≤ n := Nat.le_of_not_gt (by
      simpa only [Finset.mem_range] using hn)
    cases n with
    | zero => omega
    | succ k =>
        have hmk : m ≤ k := Nat.le_of_succ_le_succ hmn
        apply hzero (k + 1) u ω
        change (u : WithTop ℝ≥0) ≤ Γ k ω
        exact (hu.le.trans (min_le_right _ _)).trans ((hΓ ω).monotone hmk)
  have hcount_tail (n : ℕ) (hn : n ∉ Finset.range (m + 1)) :
      (if Γ n ω ≤ (u : WithTop ℝ≥0) then (1 : ℝ) else 0) = 0 := by
    have hmn : m + 1 ≤ n := Nat.le_of_not_gt (by
      simpa only [Finset.mem_range] using hn)
    apply if_neg
    intro hn_arrived
    exact (not_lt_of_ge (hcount.trans hmn)) (((hΓ ω).lt_count_iff u n).mpr hn_arrived)
  have hsum_count : ((hΓ ω).count u : ℝ) =
      ∑ n ∈ Finset.range (m + 1),
        if Γ n ω ≤ (u : WithTop ℝ≥0) then (1 : ℝ) else 0 :=
    ((hΓ ω).finite_arrivals_and_count_eq_tsum u).2.trans
      (tsum_eq_sum (s := Finset.range (m + 1)) hcount_tail)
  change ((hΓ ω).count u : ℝ) - ∑' n : ℕ, D n u ω =
    ∑ n ∈ Finset.range (m + 1),
      ((if Γ n ω ≤ (u : WithTop ℝ≥0) then (1 : ℝ) else 0) - D n u ω)
  rw [hsum_count, tsum_eq_sum (s := Finset.range (m + 1)) hzero_tail,
    Finset.sum_sub_distrib]

end ProbabilityTheory.IsNonexplosiveArrivalSequence
