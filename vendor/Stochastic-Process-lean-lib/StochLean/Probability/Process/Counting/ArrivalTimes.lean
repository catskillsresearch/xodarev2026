/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Basic
public import StochLean.Probability.Process.Stopping.RightContinuousHitting
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Actual arrival times of a nonexplosive counting process

The arrival with index `n` is Mathlib's existing `hittingAfter N (Ioi n) 0`:
it is the time of count `n + 1`, with value infinity when that arrival never
occurs. No additional arrival selector is defined. On one common path
event, these times are positive, ordered, strictly ordered whenever the
earlier arrival is finite, and tend to infinity. In particular, an eventual
infinite tail is permitted.

The actual count equals the finite-support sum of the closed arrival
indicators. The raw hitting times, not modified versions, are stopping
times under adaptedness and the usual conditions. This is the forward
count-to-arrivals representation; constructing a general count from a
given possibly terminating arrival sequence is a separate direction.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsNonexplosiveCountingProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {N : ℝ≥0 → Ω → ℕ}

/-- A count has reached level `n + 1` exactly when its actual `n`-indexed
arrival has occurred. The equivalence holds for every time on one event. -/
theorem ae_hittingAfter_le_iff (hN : IsNonexplosiveCountingProcess N P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0),
      hittingAfter N (Ioi n) 0 ω ≤ t ↔ n < N t ω := by
  filter_upwards [hN.monotonePaths, hN.rightContinuousPaths] with ω hm hr n t
  constructor
  · intro hle
    have hfin : hittingAfter N (Ioi n) 0 ω ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hle
    have hmem : n < N (hittingAfter N (Ioi n) 0 ω).untopA ω :=
      hittingAfter_mem_of_rightContinuous (isClosed_discrete (Ioi n)) hr hfin
    exact hmem.trans_le (hm (WithTop.untopA_le hle))
  · intro hlt
    exact hittingAfter_le_of_mem bot_le hlt

/-- Actual arrival times are positive and nonexplosive, and finite
arrivals have the correct count and strictly precede the next arrival.
Only the explicitly finite branch evaluates an `untopA` clock. -/
theorem ae_hittingAfter_arrival_properties (hN : IsNonexplosiveCountingProcess N P) :
    ∀ᵐ ω ∂P,
      (∀ n : ℕ, 0 < hittingAfter N (Ioi n) 0 ω) ∧
      Monotone (fun n : ℕ ↦ hittingAfter N (Ioi n) 0 ω) ∧
      (∀ n : ℕ, hittingAfter N (Ioi n) 0 ω ≠ ⊤ →
        N (hittingAfter N (Ioi n) 0 ω).untopA ω = n + 1) ∧
      (∀ n : ℕ, hittingAfter N (Ioi n) 0 ω ≠ ⊤ →
        hittingAfter N (Ioi n) 0 ω < hittingAfter N (Ioi (n + 1)) 0 ω) ∧
      Tendsto (fun n : ℕ ↦ hittingAfter N (Ioi n) 0 ω) atTop (𝓝 ⊤) := by
  filter_upwards [hN.ae_hittingAfter_le_iff, hN.initial, hN.hasCadlagPaths_real,
    hN.unitJumps] with ω he h0 hc hj
  let H (n : ℕ) := hittingAfter N (Ioi n) 0 ω
  have hpos (n : ℕ) : 0 < H n := by
    apply lt_of_not_ge
    intro hle
    have hlt : n < N 0 ω := (he n 0).mp (by simpa only [WithTop.coe_zero] using hle)
    have hz : N 0 ω = 0 := h0
    exact Nat.not_lt_zero n (hz ▸ hlt)
  have hmono : Monotone H := by
    intro n m hnm
    exact hittingAfter_anti N 0 (fun k hk ↦ hnm.trans_lt hk) ω
  have hval (n : ℕ) (hfin : H n ≠ ⊤) : N (H n).untopA ω = n + 1 := by
    let t := (H n).untopA
    have htcoe : (t : WithTop ℝ≥0) = H n := by
      change ((H n).untopA : WithTop ℝ≥0) = H n
      rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
    have ht : 0 < t := by
      apply WithTop.coe_lt_coe.mp
      simpa only [WithTop.coe_zero, htcoe] using hpos n
    have hin : n < N t ω := (he n t).mp htcoe.symm.le
    have hpre (s : ℝ≥0) (hs : s < t) : N s ω ≤ n := by
      apply le_of_not_gt
      intro hns
      have hh : (s : WithTop ℝ≥0) < H n := htcoe ▸ WithTop.coe_lt_coe.mpr hs
      exact (not_le_of_gt hh) ((he n s).mpr hns)
    have hleft : leftLimitProcess (fun s v ↦ (N s v : ℝ)) t ω ≤ (n : ℝ) := by
      let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
      apply le_of_tendsto (hc.tendsto_leftLimitProcess ht.ne')
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact_mod_cast hpre s hs
    have hjle : jumpProcess (fun s v ↦ (N s v : ℝ)) t ω ≤ 1 := by
      rcases hj t ht with h | h <;> simp only [h, zero_le_one, le_refl]
    change (N t ω : ℝ) - leftLimitProcess (fun s v ↦ (N s v : ℝ)) t ω ≤ 1 at hjle
    have hupper : N t ω ≤ n + 1 := by
      have hupperR : (N t ω : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        push_cast
        linarith only [hleft, hjle]
      exact_mod_cast hupperR
    exact Nat.le_antisymm hupper (Nat.succ_le_iff.mpr hin)
  refine ⟨hpos, hmono, hval, ?_, ?_⟩
  · intro n hfin
    apply lt_of_not_ge
    intro hle
    have htcoe : ((H n).untopA : WithTop ℝ≥0) = H n := by
      rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
    have hlt := (he (n + 1) (H n).untopA).mp (hle.trans htcoe.symm.le)
    rw [hval n hfin] at hlt
    exact (lt_irrefl (n + 1)) hlt
  · apply (WithTop.tendsto_nhds_top_iff _).mpr
    intro T
    filter_upwards [eventually_ge_atTop (N T ω)] with n hn
    exact lt_of_not_ge fun hle ↦ (not_lt_of_ge hn) ((he n T).mp hle)

/-- On every good path and every finite horizon there are only finitely
many actual arrivals; their closed indicators sum to the real count. An
infinite arrival contributes zero at every finite time. -/
theorem ae_count_eq_tsum_hittingAfter (hN : IsNonexplosiveCountingProcess N P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      {n : ℕ | hittingAfter N (Ioi n) 0 ω ≤ t}.Finite ∧
      (N t ω : ℝ) = ∑' n : ℕ, if hittingAfter N (Ioi n) 0 ω ≤ t then 1 else 0 := by
  classical
  filter_upwards [hN.ae_hittingAfter_le_iff] with ω he t
  constructor
  · have hs : {n : ℕ | hittingAfter N (Ioi n) 0 ω ≤ t} = Iio (N t ω) :=
      Set.ext fun n ↦ he n t
    rw [hs]
    exact Set.finite_Iio (N t ω)
  · simp_rw [he]
    rw [tsum_eq_sum (s := Finset.range (N t ω))]
    · have hs : (∑ n ∈ Finset.range (N t ω), if n < N t ω then (1 : ℝ) else 0) =
          ∑ n ∈ Finset.range (N t ω), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact if_pos (Finset.mem_range.mp hn)
      rw [hs]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · intro n hn
      exact if_neg (by simpa only [Finset.mem_range] using hn)

variable {F : Filtration ℝ≥0 mΩ}

/-- Every original raw arrival clock is a stopping time. Usual
completeness handles the common exceptional right-continuity event. -/
theorem isStoppingTime_hittingAfter (hN : IsNonexplosiveCountingProcess N P)
    (ha : Adapted F N) (hF : F.IsUsual P) (n : ℕ) :
    IsStoppingTime F (hittingAfter N (Ioi n) 0) :=
  ha.isStoppingTime_hittingAfter_isOpen_of_usual hF hN.rightContinuousPaths
    (isOpen_discrete (Ioi n)) 0

/-- The actual possibly infinite arrival clocks form a native localizing
sequence. No finite expectation or all-arrivals-finite hypothesis is used. -/
theorem isLocalizingSequence_hittingAfter (hN : IsNonexplosiveCountingProcess N P)
    (ha : Adapted F N) (hF : F.IsUsual P) :
    IsLocalizingSequence F (fun n : ℕ ↦ hittingAfter N (Ioi n) 0) P := by
  have hp := hN.ae_hittingAfter_arrival_properties
  exact ⟨⟨hN.isStoppingTime_hittingAfter ha hF, hp.mono fun _ hω ↦ hω.2.2.2.2⟩,
    hp.mono fun _ hω ↦ hω.2.1⟩

end ProbabilityTheory.IsNonexplosiveCountingProcess
