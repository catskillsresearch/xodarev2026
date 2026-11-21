/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalHazardInterval
public import StochLean.Probability.Process.Counting.ArrivalPrefixDurations

/-! # The finite hazard formula for literal latent-duration prefixes

For a valid arrival sequence made of literal extended duration prefixes,
the completed hazards evaluate the original latent durations. Each such
duration has a finite preceding prefix, so cancellation of the actual
absorbing gap is justified there. The pending hazard is evaluated at time
minus the actual preceding prefix. The original first interval is included.

This is pure path algebra for an arbitrary family of lifetime measures.
It does not claim that absorbing gaps remain independent after infinity,
and does not choose a new count, arrival or compensator process.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- A valid literal-prefix arrival sequence has the completed-plus-pending
hazard formula in its original latent durations, with no missing initial
interval or shifted completed-sum index. -/
theorem tsum_delayed_eCumulativeHazard_prefix_eq_completed_add_pending
    {Ω : Type*} (d : ℕ → Ω → WithTop ℝ≥0) (μ : ℕ → Measure (WithTop ℝ≥0))
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence
      (fun n ↦ ∑ j ∈ Finset.range (n + 1), d j ω)) (t : ℝ≥0) (ω : Ω) :
    let Γ := fun (n : ℕ) (v : Ω) ↦ ∑ j ∈ Finset.range (n + 1), d j v
    let L := fun n ↦
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let D := fun n ↦ stoppedProcess
      (fun (s : ℝ≥0) (v : Ω) ↦ if L n v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (μ n) (s - (L n v).untopA)).toReal else 0) (Γ n)
    let k := (hΓ ω).count t
    (∑' n, D n t ω) =
      (∑ n ∈ Finset.range k, (eCumulativeHazard (μ n) (d n ω).untopA).toReal) +
      (eCumulativeHazard (μ k) (t - (∑ j ∈ Finset.range k, d j ω).untopA)).toReal := by
  classical
  intro Γ L D k
  have hL (n : ℕ) : L n ω = ∑ j ∈ Finset.range n, d j ω := by
    cases n with
    | zero =>
        change (0 : WithTop ℝ≥0) = ∑ j ∈ Finset.range 0, d j ω
        simp only [Finset.range_zero, Finset.sum_empty]
    | succ n => rfl
  have he := tsum_delayed_eCumulativeHazard_eq_completed_add_pending
    (fun n (_ : Ω) ↦ μ n) hΓ t ω
  change (∑' n, D n t ω) =
    (∑ n ∈ Finset.range k,
      (eCumulativeHazard (μ n) (arrivalInterarrival (fun j ↦ Γ j ω) n).untopA).toReal) +
    (eCumulativeHazard (μ k) (t - (L k ω).untopA)).toReal at he
  rw [he, hL k]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnt : Γ n ω ≤ (t : WithTop ℝ≥0) :=
    ((hΓ ω).lt_count_iff t n).mp (Finset.mem_range.mp hn)
  have hprefix : (∑ j ∈ Finset.range n, d j ω) ≤ Γ n ω := by
    change (∑ j ∈ Finset.range n, d j ω) ≤ ∑ j ∈ Finset.range (n + 1), d j ω
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right bot_le
  have hfin : (∑ j ∈ Finset.range n, d j ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hprefix.trans hnt)
  rw [arrivalInterarrival_sum_range_eq_of_prefix_ne_top (fun j ↦ d j ω) n hfin]

end ProbabilityTheory
