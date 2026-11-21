/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalConstruction
public import StochLean.Probability.Process.Counting.ArrivalTimes
public import Mathlib.MeasureTheory.Measure.Dirac

/-! # Actual arrival sums and stopped counts

The existing almost-sure hitting-time representation is applied to a single
valid path on the Unit Dirac space. Exact recovery of the original arrivals
then gives their finite-support count formula, without a second summation
argument or arrival selector.

Stopping the original count at arrival `m` gives its minimum with `m + 1`.
Finite arrivals use the existing count-at-arrival theorem and monotonicity.
An infinite arrival leaves every finite observation unchanged and implies
that the original count is at most `m`; it is never evaluated as a time.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

variable {Γ : ℕ → WithTop ℝ≥0}

/-- At every finite time, only finitely many original arrivals have occurred,
and their actual closed indicators sum to the real count. -/
theorem finite_arrivals_and_count_eq_tsum
    (hΓ : IsNonexplosiveArrivalSequence Γ) (t : ℝ≥0) :
    {n : ℕ | Γ n ≤ (t : WithTop ℝ≥0)}.Finite ∧
      (hΓ.count t : ℝ) =
        ∑' n : ℕ, if Γ n ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0 := by
  let N : ℝ≥0 → Unit → ℕ := fun s _ ↦ hΓ.count s
  have hN : IsNonexplosiveCountingProcess N (Measure.dirac ()) :=
    isNonexplosiveCountingProcess_count (fun _ : Unit ↦ hΓ)
      (fun _ ↦ measurable_const) (Measure.dirac ())
  have he : ∀ s : ℝ≥0,
      {n : ℕ | hittingAfter N (Ioi n) 0 () ≤ (s : WithTop ℝ≥0)}.Finite ∧
        (N s () : ℝ) = ∑' n : ℕ,
          if hittingAfter N (Ioi n) 0 () ≤ (s : WithTop ℝ≥0) then (1 : ℝ) else 0 := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hN.ae_count_eq_tsum_hittingAfter
  simpa only [N, hΓ.hittingAfter_count] using he t

/-- Stopping at the original arrival of index `m` caps the count at `m + 1`.
The minimum clock is finite even when that arrival is infinite. -/
theorem count_min_arrival (hΓ : IsNonexplosiveArrivalSequence Γ) (m : ℕ) (t : ℝ≥0) :
    hΓ.count (min (t : WithTop ℝ≥0) (Γ m)).untopA = min (hΓ.count t) (m + 1) := by
  cases hm : Γ m with
  | top =>
      have hcount : hΓ.count t ≤ m := (hΓ.count_le_iff t m).mpr (by
        rw [hm]
        exact WithTop.coe_lt_top t)
      have hcount' : hΓ.count t ≤ m + 1 := hcount.trans (Nat.le_succ m)
      simp only [min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe,
        min_eq_left hcount']
  | coe r =>
      have hfin : Γ m ≠ ⊤ := by
        rw [hm]
        exact WithTop.coe_ne_top
      have hr : hΓ.count r = m + 1 := by
        simpa only [hm, WithTop.untopA, WithTop.untopD_coe] using
          hΓ.count_arrival_of_ne_top m hfin
      simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
      rw [hΓ.monotone_count.map_min, hr]

end ProbabilityTheory.IsNonexplosiveArrivalSequence
