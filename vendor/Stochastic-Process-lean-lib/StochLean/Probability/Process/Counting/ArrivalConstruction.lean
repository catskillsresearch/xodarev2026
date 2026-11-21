/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalSequence
public import StochLean.Probability.Process.Stopping.RightContinuousHitting

/-! # Random counts and recovery of their actual arrival times

The guarded count from `IsNonexplosiveArrivalSequence` recovers its original
extended arrival times through the existing `hittingAfter`. Equality is
proved also for an infinite arrival, without evaluating an infinite clock.

For a random sequence satisfying the path guard everywhere, the same
explicit count expression is measurable when the arrival coordinates are
measurable, and is a nonexplosive counting process. Its adaptedness is
equivalent to every original arrival being a stopping time; this equivalence
requires neither the usual conditions nor predictable arrival times.

This is an everywhere-valid construction. No claim about a raw sequence
whose path guard holds only almost everywhere is implicit in the result.
No new random count selector is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

variable {τ : ℕ → WithTop ℝ≥0}

/-- The actual count's native first hit of level `n + 1` is its original
arrival of index `n`, including the case where that arrival never occurs. -/
theorem hittingAfter_count (hτ : IsNonexplosiveArrivalSequence τ) (n : ℕ) :
    hittingAfter (fun t (_ : Unit) ↦ hτ.count t) (Ioi n) 0 () = τ n := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  constructor
  · intro hle
    have hfin : hittingAfter (fun t (_ : Unit) ↦ hτ.count t) (Ioi n) 0 () ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hle
    have hmem : n < hτ.count
        (hittingAfter (fun t (_ : Unit) ↦ hτ.count t) (Ioi n) 0 ()).untopA :=
      hittingAfter_mem_of_rightContinuous (isClosed_discrete (Ioi n))
        hτ.isRightContinuousPath_count hfin
    exact (hτ.lt_count_iff t n).mp
      (hmem.trans_le (hτ.monotone_count (WithTop.untopA_le hle)))
  · intro hle
    exact hittingAfter_le_of_mem bot_le ((hτ.lt_count_iff t n).mpr hle)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- The random count recovers every original arrival coordinate exactly,
not just an almost-everywhere version of that coordinate. -/
theorem hittingAfter_count_eq
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω)) (n : ℕ) :
    hittingAfter (fun t ω ↦ (hΓ ω).count t) (Ioi n) 0 = Γ n := by
  funext ω
  change hittingAfter (fun t (_ : Unit) ↦ (hΓ ω).count t) (Ioi n) 0 () = Γ n ω
  exact (hΓ ω).hittingAfter_count n

/-- Measurability of a count coordinate is exactly measurability of all
closed arrival events at that time. The proof uses the native measurable
upper-ray criterion for natural-number-valued functions. -/
theorem measurable_count_iff
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω)) (t : ℝ≥0) :
    Measurable (fun ω ↦ (hΓ ω).count t) ↔
      ∀ n : ℕ, MeasurableSet {ω | Γ n ω ≤ (t : WithTop ℝ≥0)} := by
  constructor
  · intro hm n
    have he : {ω | Γ n ω ≤ (t : WithTop ℝ≥0)} =
        (fun ω ↦ (hΓ ω).count t) ⁻¹' Ioi n := by
      ext ω
      exact ((hΓ ω).lt_count_iff t n).symm
    rw [he]
    exact hm measurableSet_Ioi
  · intro hm
    apply measurable_of_Ioi
    intro n
    have he : (fun ω ↦ (hΓ ω).count t) ⁻¹' Ioi n =
        {ω | Γ n ω ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      exact (hΓ ω).lt_count_iff t n
    rw [he]
    exact hm n

/-- Measurable extended arrival coordinates give measurable actual
counts, even for a sequence which eventually stays at infinity. -/
theorem measurable_count
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω))
    (hMeas : ∀ n, Measurable (Γ n)) (t : ℝ≥0) :
    Measurable (fun ω ↦ (hΓ ω).count t) :=
  (measurable_count_iff hΓ t).mpr fun n ↦ measurableSet_le (hMeas n) measurable_const

/-- The actual random count has the counting-process predicate under
any measure. Path validity is everywhere, while measurable arrivals are
an explicit, independent input; no moment or filtration is required. -/
theorem isNonexplosiveCountingProcess_count
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω))
    (hMeas : ∀ n, Measurable (Γ n)) (P : Measure Ω) :
    IsNonexplosiveCountingProcess (fun t ω ↦ (hΓ ω).count t) P := by
  refine ⟨fun t ↦ (measurable_count hΓ hMeas t).aemeasurable,
    Eventually.of_forall (fun ω ↦ (hΓ ω).count_zero),
    Eventually.of_forall (fun ω ↦ (hΓ ω).monotone_count),
    Eventually.of_forall (fun ω ↦ (hΓ ω).isRightContinuousPath_count), ?_⟩
  exact Eventually.of_forall fun ω t ht ↦ (hΓ ω).unitJumps_count t ht

/-- The actual count is adapted exactly when all its original arrival
times are stopping times. Exact closed-event/count equivalence suffices:
no completeness, right continuity of the filtration, or predictability
assumption is used. -/
theorem adapted_count_iff
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω))
    (F : Filtration ℝ≥0 mΩ) :
    Adapted F (fun t ω ↦ (hΓ ω).count t) ↔ ∀ n : ℕ, IsStoppingTime F (Γ n) := by
  constructor
  · intro ha n t
    exact (measurable_count_iff (mΩ := F t) hΓ t).mp (ha t) n
  · intro hs t
    exact (measurable_count_iff (mΩ := F t) hΓ t).mpr fun n ↦ hs n t

end ProbabilityTheory.IsNonexplosiveArrivalSequence
