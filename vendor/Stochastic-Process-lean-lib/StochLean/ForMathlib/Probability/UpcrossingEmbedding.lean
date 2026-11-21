/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Upcrossing

/-! # Upcrossings under order-preserving sampling

The existing discrete crossing times are compared by their hitting-time
minimality. Sampling need only be monotone, but every retained sample must
lie strictly before the target cutoff. The strict cutoff is essential since
the canonical count excludes its terminal index.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω : Type*} {f : ℕ → Ω → ℝ} {ω : Ω} {a b : ℝ}
  {e : ℕ → ℕ} {N M : ℕ}

private theorem upperCrossingTime_le_mapped_sampling
    (he : Monotone e) (hb : ∀ i < N, e i < M) (k : ℕ)
    (hk : upperCrossingTime a b (fun n ↦ f (e n)) N k ω < N) :
    upperCrossingTime a b f M k ω ≤
      e (upperCrossingTime a b (fun n ↦ f (e n)) N k ω) := by
  induction k with
  | zero =>
    change (0 : ℕ) ≤ e 0
    exact Nat.zero_le _
  | succ k ih =>
    have hl : lowerCrossingTime a b (fun n ↦ f (e n)) N k ω < N :=
      lowerCrossingTime_le_upperCrossingTime_succ.trans_lt hk
    have hp : upperCrossingTime a b (fun n ↦ f (e n)) N k ω < N :=
      upperCrossingTime_le_lowerCrossingTime.trans_lt hl
    have hlowMem : f (e (lowerCrossingTime a b (fun n ↦ f (e n)) N k ω)) ω ≤ a := by
      have h := stoppedValue_lowerCrossingTime hl.ne
      exact h
    have hlow : lowerCrossingTime a b f M k ω ≤
        e (lowerCrossingTime a b (fun n ↦ f (e n)) N k ω) := by
      change hittingBtwn f (Set.Iic a) (upperCrossingTime a b f M k ω) M ω ≤ _
      exact hittingBtwn_le_of_mem
        ((ih hp).trans (he upperCrossingTime_le_lowerCrossingTime)) (hb _ hl).le hlowMem
    have huMem : b ≤ f (e (upperCrossingTime a b (fun n ↦ f (e n)) N (k + 1) ω)) ω := by
      have h := stoppedValue_upperCrossingTime hk.ne
      exact h
    rw [upperCrossingTime_succ_eq]
    exact hittingBtwn_le_of_mem
      (hlow.trans (he lowerCrossingTime_le_upperCrossingTime_succ)) (hb _ hk).le huMem

/-- Adding samples cannot remove completed upcrossings. No strict monotonicity
of the sampling map is required, but retained indices must precede `M`. -/
theorem upcrossingsBefore_comp_le (hab : a < b) (he : Monotone e)
    (hb : ∀ i < N, e i < M) :
    upcrossingsBefore a b (fun n ↦ f (e n)) N ω ≤ upcrossingsBefore a b f M ω := by
  by_cases hN : 0 < N
  · have hk : upperCrossingTime a b (fun n ↦ f (e n)) N
        (upcrossingsBefore a b (fun n ↦ f (e n)) N ω) ω < N :=
      upperCrossingTime_lt_of_le_upcrossingsBefore hN hab le_rfl
    apply le_csSup (upperCrossingTime_lt_bddAbove hab)
    exact (upperCrossingTime_le_mapped_sampling he hb _ hk).trans_lt (hb _ hk)
  · have hz : N = 0 := by omega
    simp only [hz, upcrossingsBefore_zero, Nat.zero_le]

end MeasureTheory
