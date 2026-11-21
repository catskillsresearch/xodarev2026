/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalTimes

/-! # Actual counting arrivals lie on the unit-jump graph

Every finite native hitting arrival of a nonexplosive counting process is
a positive time with an actual real jump equal to one. The count is `n + 1`
at the arrival and at most `n` at every strictly earlier time. The genuine
cadlag left limit retains that bound, so the unit-jump alternative cannot
be zero.

One common path event covers all arrival indices. No filtration, finite
measure, moment bound, or all-arrivals-finite assumption is used. The
possibly infinite raw hitting times remain unchanged, and an `untopA`
clock is evaluated only in the explicitly finite branch.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsNonexplosiveCountingProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {N : ℝ≥0 → Ω → ℕ}

/-- Each actual finite arrival is a positive unit jump, on one common
event for every arrival index. Infinite arrivals require no evaluation. -/
theorem ae_hittingAfter_jump_eq_one (hN : IsNonexplosiveCountingProcess N P) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, hittingAfter N (Ioi n) 0 ω ≠ ⊤ →
      ∃ t : ℝ≥0, 0 < t ∧ hittingAfter N (Ioi n) 0 ω = (t : WithTop ℝ≥0) ∧
        jumpProcess (fun s v ↦ (N s v : ℝ)) t ω = 1 := by
  filter_upwards [hN.ae_hittingAfter_arrival_properties, hN.ae_hittingAfter_le_iff,
    hN.hasCadlagPaths_real, hN.unitJumps] with ω hp he hc hj n hfinite
  let t : ℝ≥0 := (hittingAfter N (Ioi n) 0 ω).untopA
  have htcoe : (t : WithTop ℝ≥0) = hittingAfter N (Ioi n) 0 ω := by
    dsimp only [t]
    rw [WithTop.untopA_eq_untop hfinite, WithTop.coe_untop]
  have ht : 0 < t := by
    apply WithTop.coe_lt_coe.mp
    simpa only [WithTop.coe_zero, htcoe] using hp.1 n
  have hvalue : N t ω = n + 1 := hp.2.2.1 n hfinite
  have hbefore (s : ℝ≥0) (hs : s < t) : N s ω ≤ n := by
    apply le_of_not_gt
    intro hns
    have hlt : (s : WithTop ℝ≥0) < hittingAfter N (Ioi n) 0 ω :=
      htcoe ▸ WithTop.coe_lt_coe.mpr hs
    exact (not_le_of_gt hlt) ((he n s).mpr hns)
  have hleft : leftLimitProcess (fun s v ↦ (N s v : ℝ)) t ω ≤ (n : ℝ) := by
    let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    apply le_of_tendsto (hc.tendsto_leftLimitProcess ht.ne')
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact_mod_cast hbefore s hs
  have hpositive : 0 < jumpProcess (fun s v ↦ (N s v : ℝ)) t ω := by
    change 0 < (N t ω : ℝ) - leftLimitProcess (fun s v ↦ (N s v : ℝ)) t ω
    rw [hvalue, Nat.cast_add, Nat.cast_one]
    linarith only [hleft]
  exact ⟨t, ht, htcoe.symm, (hj t ht).resolve_left (ne_of_gt hpositive)⟩

end ProbabilityTheory.IsNonexplosiveCountingProcess
