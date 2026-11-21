/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalGapClock
public import StochLean.Probability.Process.Counting.DelayedHazardSupport

/-! # Completed and pending terms in the actual arrival-hazard formula

At the actual count index, earlier hazards have reached their complete gap
and the current hazard is evaluated at the elapsed time since its birth.
The count-index formula includes time zero and every arrival endpoint.
No value at an infinite observation time is used: every completed gap and
the preceding lifetime of the pending stage are genuinely finite.

The measures may vary arbitrarily with the sample. These are pointwise
identities, independent of conditional-law, measurability or probability
hypotheses; the original stopped delayed hazard remains the expression used.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- A completed stage evaluates its hazard at its actual gap; the current
pending stage evaluates it at elapsed time from its finite preceding arrival. -/
theorem stopped_delayed_eCumulativeHazard_completed_pending
    (μ : Ω → Measure (WithTop ℝ≥0))
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    let L : Ω → WithTop ℝ≥0 :=
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let D := stoppedProcess
      (fun (s : ℝ≥0) (v : Ω) ↦ if L v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (μ v) (s - (L v).untopA)).toReal else 0) (Γ n)
    (Γ n ω ≤ (t : WithTop ℝ≥0) → D t ω =
      (eCumulativeHazard (μ ω) (arrivalInterarrival (fun k ↦ Γ k ω) n).untopA).toReal) ∧
    ((hΓ ω).count t = n → D t ω =
      (eCumulativeHazard (μ ω) (t - (L ω).untopA)).toReal) := by
  classical
  intro L D
  let S := arrivalInterarrival (fun k ↦ Γ k ω) n
  let q := t - (min (t : WithTop ℝ≥0) (L ω)).untopA
  have hclock : D t ω = (eCumulativeHazard (μ ω)
      (min (q : WithTop ℝ≥0) S).untopA).toReal := by
    simpa only [D, q, S, L, Kernel.const_apply, stoppedProcess, id_eq] using
      stoppedProcess_delayed_eCumulativeHazard_eq_arrivalInterarrival
        (Kernel.const Unit (μ ω)) (fun _ : Ω ↦ ()) hΓ n t ω
  have hLc : Nat.casesOn (motive := fun _ ↦ WithTop ℝ≥0) n 0
      (fun k ↦ Γ k ω) = L ω := by
    cases n <;> rfl
  have hcount : Γ n ω ≤ (t : WithTop ℝ≥0) ↔ S ≤ (q : WithTop ℝ≥0) := by
    simpa only [q, S, hLc] using
      (hΓ ω).arrival_le_iff_interarrival_le_elapsedTime n t
  constructor
  · intro hn
    rw [hclock, min_eq_right (hcount.mp hn)]
  · intro hn
    have hnext : (t : WithTop ℝ≥0) < Γ n ω := by
      simpa only [hn] using (hΓ ω).lt_arrival_count t
    have hgap : (q : WithTop ℝ≥0) ≤ S :=
      le_of_not_ge (fun h ↦ (not_le_of_gt hnext) (hcount.mpr h))
    have hL : L ω ≤ (t : WithTop ℝ≥0) := by
      cases n with
      | zero => exact bot_le
      | succ k =>
          change Γ k ω ≤ (t : WithTop ℝ≥0)
          apply ((hΓ ω).lt_count_iff t k).mp
          rw [hn]
          exact Nat.lt_succ_self k
    rw [hclock, min_eq_left hgap]
    simp only [WithTop.untopA, WithTop.untopD_coe, q, min_eq_right hL]

/-- The actual series is the sum of completed hazards and exactly one
pending hazard. The count-index convention includes the initial interval
and treats every arrival endpoint without omitting or doubling a jump. -/
theorem tsum_delayed_eCumulativeHazard_eq_completed_add_pending
    (μ : ℕ → Ω → Measure (WithTop ℝ≥0))
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω)) (t : ℝ≥0) (ω : Ω) :
    let L := fun n ↦
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let D := fun n ↦ stoppedProcess
      (fun (s : ℝ≥0) (v : Ω) ↦ if L n v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (μ n v) (s - (L n v).untopA)).toReal else 0) (Γ n)
    let k := (hΓ ω).count t
    (∑' n, D n t ω) =
      (∑ n ∈ Finset.range k,
        (eCumulativeHazard (μ n ω) (arrivalInterarrival (fun j ↦ Γ j ω) n).untopA).toReal) +
      (eCumulativeHazard (μ k ω) (t - (L k ω).untopA)).toReal := by
  classical
  intro L D k
  have hzero (n : ℕ) (hn : n ∉ Finset.range (k + 1)) : D n t ω = 0 := by
    have hkn : k < n := Nat.lt_of_succ_le
      (Nat.le_of_not_gt (fun h ↦ hn (Finset.mem_range.mpr h)))
    simpa only [D, L, Kernel.const_apply, stoppedProcess] using
      stoppedProcess_delayed_eCumulativeHazard_eq_zero_of_count_lt
        (Kernel.const Unit (μ n ω)) (fun _ : Ω ↦ ()) hΓ n le_rfl ω hkn
  rw [tsum_eq_sum (s := Finset.range (k + 1)) hzero, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    exact (stopped_delayed_eCumulativeHazard_completed_pending (μ n) hΓ n t ω).1
      (((hΓ ω).lt_count_iff t n).mp (Finset.mem_range.mp hn))
  · exact (stopped_delayed_eCumulativeHazard_completed_pending (μ k) hΓ k t ω).2 rfl

end ProbabilityTheory
