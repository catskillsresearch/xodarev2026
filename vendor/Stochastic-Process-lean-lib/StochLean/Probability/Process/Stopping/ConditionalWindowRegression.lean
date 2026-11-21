/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalClosedWindowLimit

/-! # Boundary regressions for uniform stopping-window probabilities -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochLean.SemimartingaleRegression

/-- A zero horizon retains the value at zero; it is not an empty supremum. -/
theorem dense_running_supremum_zero_horizon {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    denseRunningSupremum X 0 ω = ENNReal.ofReal (X 0 ω) := by
  have hz (n : ℕ) : denseTimeUpTo 0 n = 0 := min_eq_left bot_le
  simp only [denseRunningSupremum, hz, iSup_const]

/-- A deterministic jump at the right endpoint is detected by the clipped dense grid. -/
theorem dense_running_supremum_includes_terminal_jump :
    denseRunningSupremum
      (fun (t : ℝ≥0) (_ : Unit) ↦ if (1 : ℝ≥0) ≤ t then (1 : ℝ) else 0) 1 () = 1 := by
  let X : ℝ≥0 → Unit → ℝ := fun t _ ↦ if (1 : ℝ≥0) ≤ t then 1 else 0
  have hc : IsRightContinuousPath (X · ()) := by
    have h := isCadlagPath_indicator_lifetime_le
      (fun _ : Unit ↦ (1 : WithTop ℝ≥0)) (fun _ ↦ (1 : ℝ)) ()
    simpa only [X, indicator_apply, mem_ofPred_eq, ← WithTop.coe_one,
      WithTop.coe_le_coe] using h.1
  apply le_antisymm
  · exact denseRunningSupremum_le_one (fun t _ ↦ by split_ifs <;> norm_num)
  · have h := ofReal_le_denseRunningSupremum_of_rightContinuous
      (X := X) (ω := ()) (le_refl (1 : ℝ≥0)) hc
    simpa only [X, le_refl, if_true, ENNReal.ofReal_one] using h

/-- Without total inaccessibility, even arbitrarily small left-open windows can
retain supremum one: the deterministic lifetime one is already known. -/
theorem deterministic_lifetime_small_windows_have_supremum_one
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    denseRunningSupremum
      (fun t : ℝ≥0 ↦ {_ω : Unit | (t : WithTop ℝ≥0) < 1 ∧
        (1 : WithTop ℝ≥0) ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ))) 1 () = 1 := by
  let X : ℝ≥0 → Unit → ℝ := fun t ↦
    {_ω : Unit | (t : WithTop ℝ≥0) < 1 ∧
      (1 : WithTop ℝ≥0) ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator (fun _ ↦ 1)
  have hr : IsRightContinuousPath (X · ()) :=
    isRightContinuousPath_indicator_lifetime_window (fun _ : Unit ↦ 1) δ ()
  have hs : (1 - δ : ℝ≥0) < 1 := tsub_lt_self zero_lt_one hδ
  have he : X (1 - δ) () = 1 := by
    apply indicator_of_mem
    exact ⟨WithTop.coe_lt_coe.mpr hs, by
      rw [tsub_add_cancel_of_le hδ1, WithTop.coe_one]⟩
  apply le_antisymm
  · apply denseRunningSupremum_le_one
    intro t _
    exact indicator_le_self' (fun _ _ ↦ (show (0 : ℝ) ≤ 1 from zero_le_one)) _
  · have h := ofReal_le_denseRunningSupremum_of_rightContinuous
      (X := X) (ω := ()) hs.le hr
    simpa only [he, ENNReal.ofReal_one] using h

/-- A zero-width closed window vanishes at deterministic times for a totally
inaccessible lifetime; the no-atom assumption is not dropped. -/
theorem totally_inaccessible_closed_zero_width_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (t : ℝ≥0) :
    P[{ω | (t : WithTop ℝ≥0) ≤ τ ω ∧ τ ω ≤ (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ)) | F t] =ᵐ[P] 0 := by
  have h := hτ.condExp_closed_window_eq_open t 0
  have he : {ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ (t : WithTop ℝ≥0)} = ∅ := by
    ext ω
    exact iff_false_intro (fun hω ↦ (not_lt_of_ge hω.2) hω.1)
  simp only [add_zero, he, indicator_empty] at h
  change _ =ᵐ[P] P[(0 : Ω → ℝ) | F t] at h
  simpa only [condExp_zero] using h

end StochLean.SemimartingaleRegression
