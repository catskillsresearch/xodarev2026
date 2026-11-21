/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalInterarrival
public import Mathlib.Data.ENNReal.Operations

/-! # Actual arrivals from positive latent durations

The literal extended prefix sums of strictly positive durations form a
nonexplosive arrival sequence when those sums tend to infinity. Durations
may themselves be infinite; finite arrivals are strictly separated, while
an infinite duration produces the permitted absorbing arrival tail.

The actual absorbing interarrival equals its original latent duration only
when the preceding prefix is finite. This cancellation needs neither
positivity nor nonexplosion. The current duration may still be infinite.
Stage zero uses the empty preceding sum and recovers the first duration.
When the preceding prefix is infinite, the actual absorbing gap is infinity
and is not asserted to equal an arbitrary subsequent latent duration.

No arrival-time, interarrival-time or count selector is introduced. These
deterministic facts do not assert independence of the absorbing gaps.
-/

@[expose] public section

open Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- Strictly positive extended durations with diverging actual prefix sums
give the existing nonexplosive arrival predicate, including infinite tails. -/
theorem isNonexplosiveArrivalSequence_sum_range_of_pos (d : ℕ → WithTop ℝ≥0)
    (hd : ∀ n, 0 < d n)
    (hdiv : Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), d i) atTop (𝓝 ⊤)) :
    IsNonexplosiveArrivalSequence (fun n ↦ ∑ i ∈ Finset.range (n + 1), d i) := by
  have hm : Monotone (fun n ↦ ∑ i ∈ Finset.range (n + 1), d i) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Finset.sum_range_succ d (n + 1)]
    exact le_add_of_nonneg_right bot_le
  refine ⟨?_, hm, ?_, hdiv⟩
  · intro n
    apply (hd 0).trans_le
    simpa only [Nat.zero_add, Finset.sum_range_one] using hm (Nat.zero_le n)
  · intro n hn
    rw [Finset.sum_range_succ d (n + 1)]
    simpa only [add_zero] using WithTop.add_lt_add_left hn (hd (n + 1))

/-- With a genuinely finite preceding prefix, the original absorbing gap
of the literal arrival sums equals the latent duration. The current duration
may be infinite, and positivity or nonexplosion is not needed for this identity. -/
theorem arrivalInterarrival_sum_range_eq_of_prefix_ne_top
    (d : ℕ → WithTop ℝ≥0) (n : ℕ)
    (hfin : (∑ i ∈ Finset.range n, d i) ≠ ⊤) :
    arrivalInterarrival (fun k ↦ ∑ i ∈ Finset.range (k + 1), d i) n = d n := by
  cases n with
  | zero => simp only [arrivalInterarrival, Nat.zero_add, Finset.sum_range_one]
  | succ k =>
      change (if (∑ i ∈ Finset.range (k + 1), d i) = ⊤ then ⊤ else
        (∑ i ∈ Finset.range (k + 1 + 1), d i) -
          ∑ i ∈ Finset.range (k + 1), d i) = d (k + 1)
      rw [if_neg hfin, Finset.sum_range_succ d (k + 1)]
      exact ENNReal.add_sub_cancel_left hfin

end ProbabilityTheory
