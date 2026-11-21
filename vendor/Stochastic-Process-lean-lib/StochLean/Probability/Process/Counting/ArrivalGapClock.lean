/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalInterarrival
public import StochLean.Probability.Process.Counting.DelayedKernelHazard

/-! # Safe elapsed time and actual absorbing interarrival clocks

Elapsed time is expressed as `t - (min t L).untopA`. The minimum is always
finite, including when the earlier arrival is infinite. Thus elapsed time
is zero before the earlier arrival, is monotone in calendar time, and is
bounded by calendar time. No new clock or stage selector is introduced.

Strict positivity of the actual absorbing gap identifies the original
closed arrival event with the corresponding elapsed-time event. The actual
delayed kernel hazard stopped at that arrival has the same elapsed-time
representation, with no activation indicator left over. These are exact
clock identities; no conditional law, moment, path-regularity or stopping
time assumption on the kernel history is required.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A measurable extended lifetime gives a jointly measurable safe elapsed
time, monotone in calendar time and bounded by the calendar observation. -/
theorem measurable_monotone_bounded_elapsedTime_of_lifetime
    {H : Type*} {mH : MeasurableSpace H} {ℓ : H → WithTop ℝ≥0}
    (hℓ : Measurable ℓ) :
    Measurable (fun p : ℝ≥0 × H ↦
      p.1 - (min (p.1 : WithTop ℝ≥0) (ℓ p.2)).untopA) ∧
      (∀ h, Monotone (fun t : ℝ≥0 ↦
        t - (min (t : WithTop ℝ≥0) (ℓ h)).untopA)) ∧
      ∀ (t : ℝ≥0) h, t - (min (t : WithTop ℝ≥0) (ℓ h)).untopA ≤ t := by
  refine ⟨measurable_fst.sub
    (((WithTop.continuous_coe.measurable.comp measurable_fst).min
      (hℓ.comp measurable_snd)).untopA), ?_, fun _ _ ↦ tsub_le_self⟩
  intro h s t hst
  cases hℓh : ℓ h with
  | top =>
      simp only [min_eq_left le_top, WithTop.untopA,
        WithTop.untopD_coe, tsub_self, le_refl]
  | coe l =>
      simp only [← WithTop.coe_min, WithTop.untopA,
        WithTop.untopD_coe, tsub_min]
      exact tsub_le_tsub_right hst l

/-- The actual closed arrival event is the actual positive absorbing gap
event at the safe elapsed time, including infinite earlier arrivals. -/
theorem IsNonexplosiveArrivalSequence.arrival_le_iff_interarrival_le_elapsedTime
    {Γ : ℕ → WithTop ℝ≥0} (hΓ : IsNonexplosiveArrivalSequence Γ) (n : ℕ) (t : ℝ≥0) :
    let L : WithTop ℝ≥0 := n.casesOn 0 Γ
    Γ n ≤ (t : WithTop ℝ≥0) ↔ arrivalInterarrival Γ n ≤
      ((t - (min (t : WithTop ℝ≥0) L).untopA : ℝ≥0) : WithTop ℝ≥0) := by
  intro L
  have hpos := hΓ.arrivalInterarrival_properties.1 n
  have hsum : L + arrivalInterarrival Γ n = Γ n := by
    cases n with
    | zero =>
        change (0 : WithTop ℝ≥0) + Γ 0 = Γ 0
        exact zero_add _
    | succ k =>
        have he := hΓ.arrivalInterarrival_properties.2.1 (k + 1)
        rw [Finset.sum_range_succ, hΓ.arrivalInterarrival_properties.2.1 k] at he
        exact he
  rw [← hsum]
  cases hL : L with
  | top =>
      simp only [WithTop.top_add, min_eq_left le_top, WithTop.untopA,
        WithTop.untopD_coe, tsub_self, WithTop.coe_zero]
      exact iff_of_false (WithTop.not_top_le_coe t) (not_le_of_gt hpos)
  | coe l =>
      cases hS : arrivalInterarrival Γ n with
      | top =>
          simp only [WithTop.add_top, WithTop.not_top_le_coe]
      | coe u =>
          have hu : 0 < u := WithTop.coe_lt_coe.mp (by
            simpa only [hS, ← WithTop.coe_zero] using hpos)
          simp only [← WithTop.coe_add, ← WithTop.coe_min,
            WithTop.untopA, WithTop.untopD_coe, WithTop.coe_le_coe, tsub_min]
          by_cases hlt : l ≤ t
          · exact (le_tsub_iff_left hlt).symm
          · rw [tsub_eq_zero_of_le (le_of_not_ge hlt)]
            exact iff_of_false
              (fun h ↦ hlt ((le_add_of_nonneg_right (show 0 ≤ u from bot_le)).trans h))
              (not_le_of_gt hu)

/-- The original delayed kernel hazard stopped at arrival `n` is exactly
the original kernel hazard stopped at its actual absorbing gap and observed
at the safe elapsed time. Histories need not be measurable for this identity. -/
theorem stoppedProcess_delayed_eCumulativeHazard_eq_arrivalInterarrival
    {Ω K : Type*} {mK : MeasurableSpace K} {Γ : ℕ → Ω → WithTop ℝ≥0}
    (κ : Kernel K (WithTop ℝ≥0)) (Z : Ω → K)
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    let L : Ω → WithTop ℝ≥0 :=
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    stoppedProcess
      (fun (s : ℝ≥0) (v : Ω) ↦ if L v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ (Z v)) (s - (L v).untopA)).toReal else 0)
      (Γ n) t ω =
        stoppedProcess (fun s (_ : WithTop ℝ≥0) ↦
          (eCumulativeHazard (κ (Z ω)) s).toReal) id
          (t - (min (t : WithTop ℝ≥0) (L ω)).untopA)
          (arrivalInterarrival (fun k ↦ Γ k ω) n) := by
  classical
  intro L
  have hLR : ∀ v, L v ≤ Γ n v := by
    intro v
    cases n with
    | zero => exact bot_le
    | succ k => exact (hΓ v).monotone (Nat.le_succ k)
  have hgap (v : Ω) : (if L v = ⊤ then ⊤ else Γ n v - L v) =
      arrivalInterarrival (fun k ↦ Γ k v) n := by
    cases n with
    | zero =>
        change (if (0 : WithTop ℝ≥0) = ⊤ then ⊤ else Γ 0 v - 0) = Γ 0 v
        simp only [WithTop.zero_ne_top, if_false, tsub_zero]
    | succ k => rfl
  rw [stoppedProcess_delayed_eCumulativeHazard_eq_gap κ Z hLR t ω, hgap ω]
  by_cases hLt : L ω ≤ (t : WithTop ℝ≥0)
  · rw [if_pos hLt, min_eq_right hLt]
  · rw [if_neg hLt, min_eq_left (le_of_not_ge hLt)]
    have hzero : (0 : WithTop ℝ≥0) ≤ arrivalInterarrival (fun k ↦ Γ k ω) n :=
      ((hΓ ω).arrivalInterarrival_properties.1 n).le
    simp only [WithTop.untopA, WithTop.untopD_coe, tsub_self, stoppedProcess,
      id_eq, WithTop.coe_zero, min_eq_left hzero]
    change 0 = (eCumulativeHazard (κ (Z ω)) 0).toReal
    rw [eCumulativeHazard_zero, ENNReal.toReal_zero]

end ProbabilityTheory
