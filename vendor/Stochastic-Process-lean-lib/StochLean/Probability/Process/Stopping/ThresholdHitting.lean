/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.RightContinuousHitting
public import StochLean.Probability.Process.Stopping.Finite

/-! # Threshold hits and the actual trigger event

The first-hit owner remains Mathlib's `hittingAfter`. Pointwise order of real
processes gives the reverse order of their strict upper-level hitting times,
without any measurability or path-regularity assumptions.

For a first hit `H` capped at a finite horizon `ν`, the actual trigger event is
`{H ≤ ν}`. It belongs to the sigma-algebra at the capped stopping time. Only on
this event does the capped time equal the hit. Consequently, right continuity
gives the closed threshold bound only on this event. If the process vanishes
from another time `τ` onward and the threshold is positive, the capped hit is
strictly before `τ` on this same event. The fallback at `ν` has no such claim.

These are prerequisites for Protter III.10, Lemma 2, not its uniform conditional
probability estimate.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*}

/-- Increasing the process can only advance a strict upper-level first hit. -/
theorem hittingAfter_Ioi_le_of_process_le {X Y : ℝ≥0 → Ω → ℝ}
    (hXY : ∀ t ω, X t ω ≤ Y t ω) (a : ℝ) (b : ℝ≥0) (ω : Ω) :
    hittingAfter Y (Ioi a) b ω ≤ hittingAfter X (Ioi a) b ω := by
  apply WithTop.le_of_forall_lt_iff_le.mp
  intro t ht
  obtain ⟨s, hs, hXs⟩ := hittingAfter_lt_iff.mp ht
  exact (hittingAfter_lt_iff.mpr ⟨s, hs, lt_of_lt_of_le hXs (hXY s ω)⟩).le

/-- A pointwise decreasing sequence of processes has increasing first hits. -/
theorem monotone_hittingAfter_Ioi_of_antitone {R : ℕ → ℝ≥0 → Ω → ℝ}
    (hR : ∀ t ω, Antitone (fun n ↦ R n t ω)) (a : ℝ) (b : ℝ≥0) (ω : Ω) :
    Monotone (fun n ↦ hittingAfter (R n) (Ioi a) b ω) := by
  intro n m hnm
  exact hittingAfter_Ioi_le_of_process_le (fun t ω ↦ hR t ω hnm) a b ω

end MeasureTheory

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {H K : Ω → WithTop ℝ≥0}

/-- The event that a capped stopping time actually triggered is measurable at
the capped time, including a hit exactly at the horizon. -/
theorem measurableSet_truncate_trigger (hH : IsStoppingTime F H) (ν : ℝ≥0) :
    MeasurableSet[(truncate hH ν).measurableSpace] {ω | H ω ≤ ν} := by
  rw [truncate, measurableSpace_ofNotTop,
    (isStoppingTime_const F ν).measurableSpace_min hH]
  exact ⟨hH.measurableSet_stopping_time_le (isStoppingTime_const F ν),
    hH.measurableSet_le_stopping_time (isStoppingTime_const F ν)⟩

/-- The capped time is the original time on its actual trigger event. -/
theorem withTop_truncate_eq_of_le (hH : IsStoppingTime F H) {ν : ℝ≥0} {ω : Ω}
    (hω : H ω ≤ ν) : (truncate hH ν).withTop ω = H ω := by
  rw [withTop_truncate]
  exact min_eq_right hω

theorem truncate_eq_untopA_of_le (hH : IsStoppingTime F H) {ν : ℝ≥0} {ω : Ω}
    (hω : H ω ≤ ν) : truncate hH ν ω = (H ω).untopA := by
  have he := congrArg WithTop.untopA (withTop_truncate_eq_of_le hH hω)
  exact he

/-- Capping preserves pointwise order of the original stopping times. -/
theorem truncate_mono_of_le (hH : IsStoppingTime F H) (hK : IsStoppingTime F K)
    (hHK : ∀ ω, H ω ≤ K ω) (ν : ℝ≥0) (ω : Ω) :
    truncate hH ν ω ≤ truncate hK ν ω := by
  apply WithTop.coe_le_coe.mp
  change (truncate hH ν).withTop ω ≤ (truncate hK ν).withTop ω
  rw [withTop_truncate, withTop_truncate]
  exact min_le_min_left _ (hHK ω)

/-- Right continuity gives the closed threshold bound on the trigger event;
it does not assert membership in the open target. -/
theorem le_process_truncate_hittingAfter_Ioi_of_trigger {R : ℝ≥0 → Ω → ℝ}
    {a : ℝ} (hH : IsStoppingTime F (hittingAfter R (Ioi a) 0))
    (hr : ∀ ω, IsRightContinuousPath (R · ω)) {ν : ℝ≥0} {ω : Ω}
    (hω : hittingAfter R (Ioi a) 0 ω ≤ ν) : a ≤ R (truncate hH ν ω) ω := by
  have hne : hittingAfter R (Ioi a) 0 ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hω
  have hbound := hittingAfter_mem_closure_of_rightContinuous (hr ω) hne
  rw [closure_Ioi] at hbound
  rw [truncate_eq_untopA_of_le hH hω]
  exact hbound

/-- A positive threshold hit of a process that vanishes from `τ` onward is
strictly before `τ`, provided that the capped time actually triggered. -/
theorem truncate_hittingAfter_Ioi_lt_of_trigger {R : ℝ≥0 → Ω → ℝ}
    {a : ℝ} {τ : Ω → WithTop ℝ≥0}
    (hH : IsStoppingTime F (hittingAfter R (Ioi a) 0))
    (hr : ∀ ω, IsRightContinuousPath (R · ω)) (ha : 0 < a)
    (hsupport : ∀ (t : ℝ≥0) ω, τ ω ≤ t → R t ω = 0) {ν : ℝ≥0} {ω : Ω}
    (hω : hittingAfter R (Ioi a) 0 ω ≤ ν) : (truncate hH ν).withTop ω < τ ω := by
  apply lt_of_not_ge
  intro hle
  have hzero := hsupport (truncate hH ν ω) ω hle
  have hbound := le_process_truncate_hittingAfter_Ioi_of_trigger hH hr hω
  rw [hzero] at hbound
  exact (not_le_of_gt ha) hbound

end ProbabilityTheory.FiniteStoppingTime

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  [F.IsRightContinuous] {R : ℝ≥0 → Ω → ℝ} {a : ℝ} {τ : Ω → WithTop ℝ≥0}

/-- The measurable trigger event and its valid pathwise consequences for the
first strict upper-level hit of a right-continuous adapted process. -/
theorem Adapted.truncate_hittingAfter_Ioi_on_trigger (hR : Adapted F R)
    (hr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (R · ω)) (ha : 0 < a)
    (hsupport : ∀ (t : ℝ≥0) ω, τ ω ≤ t → R t ω = 0) (ν : ℝ≥0) :
    let hH := hR.isStoppingTime_hittingAfter_isOpen hr (isOpen_Ioi (a := a)) 0
    let σ := ProbabilityTheory.FiniteStoppingTime.truncate hH ν
    MeasurableSet[σ.measurableSpace] {ω | hittingAfter R (Ioi a) 0 ω ≤ ν} ∧
      ∀ ω, hittingAfter R (Ioi a) 0 ω ≤ ν →
        σ.withTop ω = hittingAfter R (Ioi a) 0 ω ∧
          a ≤ R (σ ω) ω ∧ σ.withTop ω < τ ω := by
  intro hH σ
  refine ⟨ProbabilityTheory.FiniteStoppingTime.measurableSet_truncate_trigger hH ν, ?_⟩
  intro ω hω
  exact ⟨ProbabilityTheory.FiniteStoppingTime.withTop_truncate_eq_of_le hH hω,
    ProbabilityTheory.FiniteStoppingTime.le_process_truncate_hittingAfter_Ioi_of_trigger
      hH hr hω,
    ProbabilityTheory.FiniteStoppingTime.truncate_hittingAfter_Ioi_lt_of_trigger
      hH hr ha hsupport hω⟩

end MeasureTheory
