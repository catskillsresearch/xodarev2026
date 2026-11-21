/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ConditionalLifetimeHazard
public import StochLean.Probability.Process.Path.CadlagTimeChange
public import Mathlib.Topology.Algebra.Ring.Real

/-! # Actual conditional-hazard paths at a safe elapsed-time clock

The actual conditional-lifetime hazard already has a single full-measure
event on which every finite observation is finite and its real path is
monotone and cadlag. On that same event it can be observed at elapsed time
`t - (min t L).untopA` for any extended starting lifetime `L`.

At a finite starting lifetime this is the continuous monotone truncated
translation `t - l`. At an infinite starting lifetime it is identically
zero. Only a finite minimum is converted by `untopA`; no finite value is
assigned to an infinite starting time. Path regularity needs no measurability
of `L`, and no new hazard, conditional distribution or process is selected.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

private theorem continuous_monotone_elapsedTime (l : WithTop ℝ≥0) :
    Continuous (fun t : ℝ≥0 ↦ t - (min (t : WithTop ℝ≥0) l).untopA) ∧
      Monotone (fun t : ℝ≥0 ↦ t - (min (t : WithTop ℝ≥0) l).untopA) := by
  cases l using WithTop.recTopCoe with
  | top =>
      simp only [min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, tsub_self]
      exact ⟨continuous_const, monotone_const⟩
  | coe l =>
      simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, tsub_min]
      exact ⟨continuous_id.sub continuous_const, fun _ _ hst ↦ tsub_le_tsub_right hst l⟩

variable {Ω K : Type*} {mΩ : MeasurableSpace Ω} {mK : MeasurableSpace K}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Ω → K} {τ : Ω → WithTop ℝ≥0}

/-- The original conditional-lifetime stopped hazard observed at safe
elapsed time is genuinely finite at every finite calendar time and has
monotone cadlag paths on the original common full-measure event. The starting
lifetime is arbitrary; its measurability is not needed for these path facts. -/
theorem ae_stopped_eCumulativeHazard_condDistrib_elapsedTime_paths
    (hH : Measurable H) (hτ : Measurable τ) (L : Ω → WithTop ℝ≥0) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let κ := condDistrib τ H P
    let q := fun (t : ℝ≥0) ω ↦ t - (min (t : WithTop ℝ≥0) (L ω)).untopA
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, stoppedProcess
        (fun r v ↦ eCumulativeHazard (κ (H v)) r) τ (q t ω) ω ≠ ∞) ∧
      Monotone (fun t ↦ stoppedProcess
        (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal) τ (q t ω) ω) ∧
      IsCadlagPath (fun t ↦ stoppedProcess
        (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal) τ (q t ω) ω) := by
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  let q := fun (t : ℝ≥0) ω ↦ t - (min (t : WithTop ℝ≥0) (L ω)).untopA
  filter_upwards [ae_stopped_eCumulativeHazard_condDistrib_paths (P := P) hH hτ]
    with ω hω
  obtain ⟨hcq, hmq⟩ := continuous_monotone_elapsedTime (L ω)
  exact ⟨fun t ↦ hω.1 (q t ω), hω.2.1.comp hmq,
    hω.2.2.1.isCadlagPath_comp_of_monotone hω.2.1 hcq hmq⟩

end ProbabilityTheory
