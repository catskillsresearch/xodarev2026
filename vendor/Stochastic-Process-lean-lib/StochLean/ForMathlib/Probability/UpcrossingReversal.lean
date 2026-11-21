/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Upcrossing

/-! # Native upcrossings under time reversal and negation

The proof adapts the audited internal `TimeReversalCrossing` implementation.
Reversing a completed crossing exchanges its two endpoints. The reversed
count uses cutoff N+1: a crossing starting at zero can finish at N after
reversal, and the native strict-before-N count would omit that endpoint.
No separate reversal or downcrossing owner is introduced.
-/

@[expose] public section

namespace MeasureTheory

private theorem upperCrossingTime_neg_reverse_le_sub
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (N k m : ℕ) (ω : Ω)
    (hm : m ≤ k) (hk : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (fun n ω ↦ -X (N - n) ω) (N + 1) m ω ≤
      N - lowerCrossingTime a b X N (k - m) ω := by
  let Y : ℕ → Ω → ℝ := fun n ω ↦ -X (N - n) ω
  have hc (j : ℕ) (hj : j ≤ k) : upperCrossingTime a b X N j ω < N :=
    (upperCrossingTime_mono hj).trans_lt hk
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    let j := k - (m + 1)
    have hm' : m ≤ k := by omega
    have hj : j + 1 = k - m := by dsimp [j]; omega
    have hjk : j + 1 ≤ k := by omega
    let σ := upperCrossingTime a b X N (j + 1) ω
    let τ := lowerCrossingTime a b X N j ω
    have hσ : σ < N := hc (j + 1) hjk
    have hτσ : τ ≤ σ := lowerCrossingTime_le_upperCrossingTime_succ
    have hτ : τ < N := hτσ.trans_lt hσ
    have hxσ : b ≤ X σ ω := stoppedValue_upperCrossingTime hσ.ne
    have hxτ : X τ ω ≤ a := stoppedValue_lowerCrossingTime hτ.ne
    have hyσ : Y (N - σ) ω ≤ -b := by
      dsimp only [Y]
      rw [Nat.sub_sub_self hσ.le]
      exact neg_le_neg hxσ
    have hyτ : -a ≤ Y (N - τ) ω := by
      dsimp only [Y]
      rw [Nat.sub_sub_self hτ.le]
      exact neg_le_neg hxτ
    have hstart : upperCrossingTime (-b) (-a) Y (N + 1) m ω ≤ N - σ := by
      have hi := ih hm'
      rw [← hj] at hi
      exact hi.trans (Nat.sub_le_sub_left upperCrossingTime_le_lowerCrossingTime N)
    have hl : lowerCrossingTime (-b) (-a) Y (N + 1) m ω ≤ N - σ :=
      hittingBtwn_le_of_mem hstart (Nat.sub_le N σ |>.trans (Nat.le_succ N)) hyσ
    have hu : lowerCrossingTime (-b) (-a) Y (N + 1) m ω ≤ N - τ :=
      hl.trans (Nat.sub_le_sub_left hτσ N)
    change upperCrossingTime (-b) (-a) Y (N + 1) (m + 1) ω ≤ N - τ
    rw [upperCrossingTime_succ_eq]
    exact hittingBtwn_le_of_mem hu (Nat.sub_le N τ |>.trans (Nat.le_succ N)) hyτ

theorem upperCrossingTime_neg_reverse_le
    {Ω : Type*} {X : ℕ → Ω → ℝ} {a b : ℝ} {N k : ℕ} {ω : Ω}
    (hk : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (fun n ω ↦ -X (N - n) ω) (N + 1) k ω ≤ N :=
  (upperCrossingTime_neg_reverse_le_sub X a b N k k ω le_rfl hk).trans (Nat.sub_le N _)

theorem upcrossingsBefore_le_neg_reverse
    {Ω : Type*} {X : ℕ → Ω → ℝ} {a b : ℝ} (hab : a < b) (N : ℕ) (ω : Ω) :
    upcrossingsBefore a b X N ω ≤
      upcrossingsBefore (-b) (-a) (fun n ω ↦ -X (N - n) ω) (N + 1) ω := by
  by_cases hN : 0 < N
  · have hk := upperCrossingTime_lt_of_le_upcrossingsBefore (f := X) (ω := ω)
      hN hab le_rfl
    apply le_csSup (upperCrossingTime_lt_bddAbove (neg_lt_neg hab))
    exact Nat.lt_succ_of_le (upperCrossingTime_neg_reverse_le hk)
  · have hz : N = 0 := by omega
    simp only [hz, upcrossingsBefore_zero, Nat.zero_le]

end MeasureTheory
