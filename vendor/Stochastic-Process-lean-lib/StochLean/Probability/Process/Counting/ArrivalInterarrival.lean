/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalSequence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Algebra.Order.Sub.WithTop

/-! # Actual interarrival durations of possibly terminating arrival sequences

The first gap is the first positive arrival, whose index is zero. Later
gaps are the actual extended nonnegative differences as long as the
previous arrival is finite. After a previous infinite arrival, the actual
gap is explicitly infinity rather than the totalized value of infinity
minus infinity.

Measurable arrival coordinates give measurable gap coordinates. For each
valid nonexplosive arrival path, all gaps are strictly positive and their
finite prefix sums recover the original arrivals, including infinite
arrivals. No new arrival-time or count selector is introduced.

These are actual gaps with an absorbing infinite tail. They are not an
independent latent sequence of durations: no independence claim follows
from the construction, including after an arrival becomes infinite.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- Actual interarrival durations, with an explicit absorbing infinite
tail after the previous arrival is infinite. Index zero is the first
arrival, not a fictitious arrival at the initial time. -/
noncomputable def arrivalInterarrival (Γ : ℕ → WithTop ℝ≥0) : ℕ → WithTop ℝ≥0 := by
  classical
  exact fun n ↦ match n with
    | 0 => Γ 0
    | k + 1 => if Γ k = ⊤ then ⊤ else Γ (k + 1) - Γ k

/-- The actual gap coordinates are measurable under coordinatewise
measurability of the original arrivals; no path-validity or probability
assumption is needed for this measurable construction. -/
theorem measurable_arrivalInterarrival
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ n, Measurable (Γ n)) (n : ℕ) :
    Measurable (fun ω ↦ arrivalInterarrival (fun k ↦ Γ k ω) n) := by
  classical
  cases n with
  | zero => exact hΓ 0
  | succ n =>
      change Measurable (fun ω ↦ if Γ n ω = ⊤ then ⊤ else Γ (n + 1) ω - Γ n ω)
      let : MeasurableSub₂ (WithTop ℝ≥0) := inferInstanceAs (MeasurableSub₂ ℝ≥0∞)
      exact Measurable.ite (measurableSet_eq_fun (hΓ n) measurable_const)
        measurable_const ((hΓ (n + 1)).sub (hΓ n))

/-- On every valid arrival path, the actual gaps are strictly positive,
their prefix sums recover every original arrival, and the infinite tail
is explicit. The prefix identity is proved also when a previous arrival
is infinite; it is not a finite-time telescoping assumption. -/
theorem IsNonexplosiveArrivalSequence.arrivalInterarrival_properties
    {Γ : ℕ → WithTop ℝ≥0} (hΓ : IsNonexplosiveArrivalSequence Γ) :
    (∀ n, 0 < arrivalInterarrival Γ n) ∧
      (∀ n, ∑ i ∈ Finset.range (n + 1), arrivalInterarrival Γ i = Γ n) ∧
      (∀ n, Γ n = ⊤ → arrivalInterarrival Γ (n + 1) = ⊤) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hΓ.positive 0
    | succ n =>
        change 0 < if Γ n = ⊤ then ⊤ else Γ (n + 1) - Γ n
        by_cases hn : Γ n = ⊤
        · rw [if_pos hn]
          exact WithTop.coe_lt_top (0 : ℝ≥0)
        · rw [if_neg hn]
          exact tsub_pos_iff_lt.mpr (hΓ.strictSuccessor n hn)
  · intro n
    induction n with
    | zero => simp only [Nat.zero_add, Finset.sum_range_one, arrivalInterarrival]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        change Γ n + (if Γ n = ⊤ then ⊤ else Γ (n + 1) - Γ n) = Γ (n + 1)
        by_cases hn : Γ n = ⊤
        · have hn' : Γ (n + 1) = ⊤ :=
            top_unique (hn ▸ hΓ.monotone (Nat.le_succ n))
          rw [if_pos hn, hn, hn', WithTop.top_add]
        · rw [if_neg hn]
          exact add_tsub_cancel_of_le (hΓ.monotone (Nat.le_succ n))
  · intro n hn
    simp only [arrivalInterarrival, if_pos hn]

end ProbabilityTheory
