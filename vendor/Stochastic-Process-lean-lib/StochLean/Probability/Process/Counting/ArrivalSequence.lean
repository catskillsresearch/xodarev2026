/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Basic
public import StochLean.Probability.Process.Poisson.Constructions
public import Mathlib.Topology.Order.WithTop

/-! # Counts of possibly terminating nonexplosive arrival sequences

The raw arrival data are a sequence of extended nonnegative times. The
predicate below permits an infinite tail, including the sequence constantly
equal to infinity. Finite arrivals are strictly separated and no finite
time contains infinitely many arrivals.

Only on this proved nonexplosive domain is the count defined, as the least
index of an arrival strictly after the query time. There is no fallback
count for explosive data, no independent candidate count, and no second
arrival-time selector. The deterministic count is zero-initial,
right-continuous and increasing with unit positive-time jumps.

The existing positive-interarrival Poisson construction is a strict
all-finite special case, and its original count agrees with this count.
Random lifting and recovery of the original arrivals are separate steps.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

/-- Positive, ordered and nonexplosive arrival times, permitting an
eventual infinite tail. Strict separation is required only after an
actual finite arrival. -/
structure IsNonexplosiveArrivalSequence (τ : ℕ → WithTop ℝ≥0) : Prop where
  positive : ∀ n, 0 < τ n
  monotone : Monotone τ
  strictSuccessor : ∀ n, τ n ≠ ⊤ → τ n < τ (n + 1)
  tendsto_top : Tendsto τ atTop (𝓝 ⊤)

namespace IsNonexplosiveArrivalSequence

variable {τ : ℕ → WithTop ℝ≥0}

/-- Nonexplosion supplies an actual next index beyond every finite time. -/
theorem exists_arrival_gt (hτ : IsNonexplosiveArrivalSequence τ) (t : ℝ≥0) :
    ∃ n, (t : WithTop ℝ≥0) < τ n :=
  ((WithTop.tendsto_nhds_top_iff _).mp hτ.tendsto_top t).exists

/-- The count of a proved nonexplosive arrival sequence is the least
index whose arrival has not occurred. This definition has no value on
arbitrary data without the nonexplosion witness. -/
noncomputable def count (hτ : IsNonexplosiveArrivalSequence τ) (t : ℝ≥0) : ℕ :=
  Nat.find (hτ.exists_arrival_gt t)

/-- The next indexed arrival lies strictly after the query time. -/
theorem lt_arrival_count (hτ : IsNonexplosiveArrivalSequence τ) (t : ℝ≥0) :
    (t : WithTop ℝ≥0) < τ (hτ.count t) :=
  Nat.find_spec (hτ.exists_arrival_gt t)

/-- The actual count is at most `n` exactly before the arrival of index
`n`. This remains valid when that arrival is infinite. -/
theorem count_le_iff (hτ : IsNonexplosiveArrivalSequence τ) (t : ℝ≥0) (n : ℕ) :
    hτ.count t ≤ n ↔ (t : WithTop ℝ≥0) < τ n := by
  constructor
  · intro h
    exact (hτ.lt_arrival_count t).trans_le (hτ.monotone h)
  · intro h
    exact Nat.find_min' (hτ.exists_arrival_gt t) h

/-- Closed arrival events are exactly strict inequalities for the count. -/
theorem lt_count_iff (hτ : IsNonexplosiveArrivalSequence τ) (t : ℝ≥0) (n : ℕ) :
    n < hτ.count t ↔ τ n ≤ (t : WithTop ℝ≥0) := by
  simpa only [not_le, not_lt] using not_congr (hτ.count_le_iff t n)

/-- An actual finite arrival has count exactly `n + 1`. The infinite
branch is deliberately excluded before applying `untopA`. -/
theorem count_arrival_of_ne_top (hτ : IsNonexplosiveArrivalSequence τ) (n : ℕ)
    (hfin : τ n ≠ ⊤) : hτ.count (τ n).untopA = n + 1 := by
  have he : ((τ n).untopA : WithTop ℝ≥0) = τ n := by
    rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
  apply Nat.le_antisymm
  · apply (hτ.count_le_iff _ (n + 1)).mpr
    rw [he]
    exact hτ.strictSuccessor n hfin
  · apply Nat.succ_le_iff.mpr
    exact (hτ.lt_count_iff _ n).mpr he.symm.le

/-- Positive arrival times give a zero initial count. -/
@[simp] theorem count_zero (hτ : IsNonexplosiveArrivalSequence τ) : hτ.count 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (hτ.count_le_iff 0 0).mpr
  simpa only [WithTop.coe_zero] using hτ.positive 0

/-- The count increases with deterministic time. -/
theorem monotone_count (hτ : IsNonexplosiveArrivalSequence τ) : Monotone hτ.count := by
  intro s t hst
  apply (hτ.count_le_iff s (hτ.count t)).mpr
  exact (WithTop.coe_le_coe.mpr hst).trans_lt (hτ.lt_arrival_count t)

/-- The next actual arrival supplies a right neighborhood on which the
count is constant. An infinite next arrival gives the same conclusion. -/
theorem isRightContinuousPath_count (hτ : IsNonexplosiveArrivalSequence τ) :
    IsRightContinuousPath hτ.count := by
  intro t
  obtain ⟨b, htb, hb⟩ : ∃ b : ℝ≥0, t < b ∧ (b : WithTop ℝ≥0) ≤ τ (hτ.count t) := by
    cases he : τ (hτ.count t) with
    | top => exact ⟨t + 1, lt_add_one t, le_top⟩
    | coe b =>
      refine ⟨b, ?_, le_rfl⟩
      exact WithTop.coe_lt_coe.mp (he ▸ hτ.lt_arrival_count t)
  have heq : hτ.count =ᶠ[𝓝[Ici t] t] fun _ ↦ hτ.count t := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htb), self_mem_nhdsWithin]
      with s hsb hts
    apply Nat.le_antisymm
    · apply (hτ.count_le_iff s (hτ.count t)).mpr
      exact (WithTop.coe_lt_coe.mpr hsb).trans_le hb
    · exact hτ.monotone_count hts
  exact continuousWithinAt_const.congr_of_eventuallyEq heq rfl

/-- The real count has actual finite left limits by monotonicity. -/
theorem isCadlagPath_count_real (hτ : IsNonexplosiveArrivalSequence τ) :
    IsCadlagPath (fun t ↦ (hτ.count t : ℝ)) := by
  have hm : Monotone (fun t ↦ (hτ.count t : ℝ)) := by
    intro s t hst
    change (hτ.count s : ℝ) ≤ (hτ.count t : ℝ)
    exact_mod_cast hτ.monotone_count hst
  refine ⟨fun t ↦ ?_, fun t _ ↦ ⟨Function.leftLim (fun s ↦ (hτ.count s : ℝ)) t,
    hm.tendsto_leftLim t⟩⟩
  have hcast : Continuous (fun n : ℕ ↦ (n : ℝ)) := continuous_of_discreteTopology
  exact hcast.continuousAt.comp_continuousWithinAt (hτ.isRightContinuousPath_count t)

private theorem leftLimit_count_eq_of_interval (hτ : IsNonexplosiveArrivalSequence τ)
    {b t : ℝ≥0} (hbt : b < t) (k : ℕ)
    (hk : ∀ s : ℝ≥0, b < s → s < t → hτ.count s = k) :
    leftLimitProcess (fun s (_ : Unit) ↦ (hτ.count s : ℝ)) t () = (k : ℝ) := by
  have ht : t ≠ 0 := (bot_le.trans_lt hbt).ne'
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨b, hbt⟩
  rw [leftLimitProcess, if_neg ht]
  apply leftLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hbt), self_mem_nhdsWithin]
    with s hbs hst
  exact (congrArg (fun n : ℕ ↦ (n : ℝ)) (hk s hbs hst)).symm

/-- Every positive-time jump of the actual count is either zero or one.
The existing process jump is evaluated on the deterministic Unit path;
no new jump convention or path representation is introduced. -/
theorem unitJumps_count (hτ : IsNonexplosiveArrivalSequence τ) (t : ℝ≥0) (ht : 0 < t) :
    jumpProcess (fun s (_ : Unit) ↦ (hτ.count s : ℝ)) t () = 0 ∨
      jumpProcess (fun s (_ : Unit) ↦ (hτ.count s : ℝ)) t () = 1 := by
  cases hk : hτ.count t with
  | zero =>
    have hl := hτ.leftLimit_count_eq_of_interval ht 0 (fun s _ hst ↦
      Nat.eq_zero_of_le_zero (by simpa only [hk] using hτ.monotone_count hst.le))
    left
    change (hτ.count t : ℝ) - _ = 0
    rw [hk, hl, Nat.cast_zero, sub_self]
  | succ n =>
    have hat : τ n ≤ (t : WithTop ℝ≥0) :=
      (hτ.lt_count_iff t n).mp (by rw [hk]; exact Nat.lt_succ_self n)
    rcases hat.lt_or_eq with hlt | heq
    · have hfin : τ n ≠ ⊤ := ne_top_of_lt hlt
      have hb : ((τ n).untopA : WithTop ℝ≥0) = τ n := by
        rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
      have hbt : (τ n).untopA < t :=
        WithTop.coe_lt_coe.mp (by simpa only [hb] using hlt)
      have hl := hτ.leftLimit_count_eq_of_interval hbt (n + 1) (by
        intro s hbs hst
        apply Nat.le_antisymm
        · simpa only [hk] using hτ.monotone_count hst.le
        · apply Nat.succ_le_iff.mpr
          apply (hτ.lt_count_iff s n).mpr
          rw [← hb]
          exact (WithTop.coe_lt_coe.mpr hbs).le)
      left
      change (hτ.count t : ℝ) - _ = 0
      rw [hk, hl]
      exact sub_self _
    · cases n with
      | zero =>
        have hl := hτ.leftLimit_count_eq_of_interval ht 0 (by
          intro s _ hst
          apply Nat.eq_zero_of_le_zero
          apply (hτ.count_le_iff s 0).mpr
          rw [heq]
          exact WithTop.coe_lt_coe.mpr hst)
        right
        change (hτ.count t : ℝ) - _ = 1
        rw [hk, hl]
        norm_num
      | succ m =>
        have hprevFin : τ m ≠ ⊤ :=
          ne_top_of_le_ne_top WithTop.coe_ne_top
            ((hτ.monotone (Nat.le_succ m)).trans hat)
        have hprevlt : τ m < (t : WithTop ℝ≥0) :=
          (hτ.strictSuccessor m hprevFin).trans_eq heq
        have hb : ((τ m).untopA : WithTop ℝ≥0) = τ m := by
          rw [WithTop.untopA_eq_untop hprevFin, WithTop.coe_untop]
        have hbt : (τ m).untopA < t :=
          WithTop.coe_lt_coe.mp (by simpa only [hb] using hprevlt)
        have hl := hτ.leftLimit_count_eq_of_interval hbt (m + 1) (by
          intro s hbs hst
          apply Nat.le_antisymm
          · apply (hτ.count_le_iff s (m + 1)).mpr
            rw [heq]
            exact WithTop.coe_lt_coe.mpr hst
          · apply Nat.succ_le_iff.mpr
            apply (hτ.lt_count_iff s m).mpr
            rw [← hb]
            exact (WithTop.coe_lt_coe.mpr hbs).le)
        right
        change (hτ.count t : ℝ) - _ = 1
        rw [hk, hl]
        push_cast
        ring

end IsNonexplosiveArrivalSequence

namespace PoissonProcess.DivergentArrivalSequence

/-- The existing strictly positive-interarrival construction is the
all-finite special case of nonexplosive extended arrival data. -/
theorem isNonexplosiveArrivalSequence_eventTime (a : DivergentArrivalSequence) :
    IsNonexplosiveArrivalSequence (fun n ↦ (a.eventTime n : WithTop ℝ≥0)) := by
  have hpos0 : 0 < a.eventTime 0 := by
    simpa only [eventTime, arrivalTime, Nat.zero_add, Finset.sum_range_one] using a.positive 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have hp := hpos0.trans_le (a.strictMono_eventTime.monotone (Nat.zero_le n))
    simpa only [WithTop.coe_zero] using WithTop.coe_lt_coe.mpr hp
  · intro n m hnm
    exact WithTop.coe_le_coe.mpr (a.strictMono_eventTime.monotone hnm)
  · intro n _
    exact WithTop.coe_lt_coe.mpr (a.strictMono_eventTime (Nat.lt_succ_self n))
  · apply (WithTop.tendsto_nhds_top_iff _).mpr
    intro T
    have hlim : Tendsto a.eventTime atTop atTop :=
      a.tendsto_arrivalTime.comp (tendsto_add_atTop_nat 1)
    filter_upwards [(tendsto_atTop.mp hlim) (T + 1)] with n hn
    exact WithTop.coe_lt_coe.mpr ((lt_add_one T).trans_le hn)

/-- On the old all-finite domain the guarded extended-arrival count is
exactly the existing count, rather than a competing representation. -/
theorem count_eq_nonexplosiveArrivalSequence_count (a : DivergentArrivalSequence) :
    a.count = a.isNonexplosiveArrivalSequence_eventTime.count := by
  funext t
  apply Nat.le_antisymm
  · apply (a.count_le_iff t _).mpr
    exact WithTop.coe_lt_coe.mp (a.isNonexplosiveArrivalSequence_eventTime.lt_arrival_count t)
  · apply (a.isNonexplosiveArrivalSequence_eventTime.count_le_iff t _).mpr
    exact WithTop.coe_lt_coe.mpr (a.lt_eventTime_count t)

end PoissonProcess.DivergentArrivalSequence

end ProbabilityTheory
