/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.DelayedKernelHazard
public import StochLean.Probability.Process.Counting.ArrivalSequence

/-! # Exact zero support of the original delayed hazard

The original stopped delayed kernel hazard vanishes before and at its
starting lifetime. Even when activation holds at the stopped observation,
the observation must equal the starting lifetime and its actual age is zero.
The cumulative hazard excludes the initial atom and is therefore zero there.

For actual nonexplosive arrivals, every stage strictly beyond the count at a
finite horizon vanishes throughout that horizon. The current stage, whose
index equals the count, is deliberately retained. These are pointwise support
identities requiring neither a measure nor stopping or measurability hypotheses.
No new process, stage or clock is defined.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω K : Type*} {mK : MeasurableSpace K}

/-- The actual stopped delayed hazard is zero before and at its starting
lifetime. In particular the equality endpoint is included, and an infinite
starting lifetime never contributes at a finite observation. -/
theorem stoppedProcess_delayed_eCumulativeHazard_eq_zero_of_le
    (κ : Kernel K (WithTop ℝ≥0)) (Z : Ω → K)
    {L R : Ω → WithTop ℝ≥0} {t : ℝ≥0} {ω : Ω}
    (htL : (t : WithTop ℝ≥0) ≤ L ω) :
    stoppedProcess
      (fun (s : ℝ≥0) v ↦ if L v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ (Z v)) (s - (L v).untopA)).toReal else 0)
      R t ω = 0 := by
  classical
  let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (R ω)).untopA
  have hut : u ≤ t := WithTop.untopA_le (min_le_left _ _)
  change (if L ω ≤ (u : WithTop ℝ≥0)
    then (eCumulativeHazard (κ (Z ω)) (u - (L ω).untopA)).toReal else 0) = 0
  by_cases hLu : L ω ≤ (u : WithTop ℝ≥0)
  · have huL : (u : WithTop ℝ≥0) = L ω :=
      le_antisymm ((WithTop.coe_le_coe.mpr hut).trans htL) hLu
    have hage : u - (L ω).untopA = 0 := by
      rw [← huL]
      simp only [WithTop.untopA, WithTop.untopD_coe, tsub_self]
    rw [if_pos hLu, hage, eCumulativeHazard_zero, ENNReal.toReal_zero]
  · exact if_neg hLu

/-- Every stage strictly beyond the actual arrival count at a horizon
vanishes throughout that horizon. The stage equal to the count is not
discarded. The conclusion also covers terminating infinite arrival tails. -/
theorem stoppedProcess_delayed_eCumulativeHazard_eq_zero_of_count_lt
    (κ : Kernel K (WithTop ℝ≥0)) (Z : Ω → K)
    {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (n : ℕ) {t T : ℝ≥0} (htT : t ≤ T) (ω : Ω)
    (hn : (hΓ ω).count T < n) :
    let L : Ω → WithTop ℝ≥0 :=
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    stoppedProcess
      (fun (s : ℝ≥0) v ↦ if L v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ (Z v)) (s - (L v).untopA)).toReal else 0)
      (Γ n) t ω = 0 := by
  intro L
  apply stoppedProcess_delayed_eCumulativeHazard_eq_zero_of_le κ Z
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ k =>
      have hT : (T : WithTop ℝ≥0) < Γ k ω :=
        ((hΓ ω).count_le_iff T k).mp (Nat.le_of_lt_succ hn)
      exact (WithTop.coe_le_coe.mpr htT).trans hT.le

end ProbabilityTheory
