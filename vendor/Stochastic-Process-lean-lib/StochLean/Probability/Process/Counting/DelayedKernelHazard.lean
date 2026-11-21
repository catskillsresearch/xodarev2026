/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.KernelHazard
public import StochLean.Probability.Process.Stopping.DelayedPredictable
public import Mathlib.Algebra.Order.Sub.WithTop

/-! # Delayed activation and calendar stopping of the actual kernel hazard

A kernel history measurable at an ordinary stopping time becomes available
strictly afterwards. Since the original cumulative hazard vanishes at age
zero, its closed delayed activation is predictable. Stopping this actual
process at another ordinary stopping time preserves predictability. No
initial measurability of the history or predictability of either stopping
time is assumed.

For ordered calendar lifetimes, the stopped delayed process equals the
original kernel hazard stopped at the actual extended gap, on the event
that the earlier calendar lifetime has occurred. An infinite earlier
lifetime gives an explicitly infinite gap and never activates the process;
no infinite calendar value is evaluated. Equal lifetimes give zero age,
and the integration convention excludes the initial atom.

These are exact measurability and clock identities for the original real
representative. They do not assert its finiteness, path regularity or
integrability without the separate hazard hypotheses, and do not assert
that the gap is a stopping time in the original calendar filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω K : Type*} {mΩ : MeasurableSpace Ω} {mK : MeasurableSpace K}
  {F : Filtration ℝ≥0 mΩ} {L R : Ω → WithTop ℝ≥0} {Z : Ω → K}

/-- A kernel hazard activated using actual stopped-field history, then
stopped at an ordinary calendar stopping time, is strongly predictable. -/
theorem isStronglyPredictable_stopped_delayed_eCumulativeHazard
    (κ : Kernel K (WithTop ℝ≥0)) [IsSFiniteKernel κ]
    (hL : IsStoppingTime F L) (hR : IsStoppingTime F R)
    (hZ : Measurable[hL.measurableSpace] Z) (z₀ : K) :
    IsStronglyPredictable F (stoppedProcess
      (fun t ω ↦ if L ω ≤ (t : WithTop ℝ≥0)
        then (eCumulativeHazard (κ (Z ω)) (t - (L ω).untopA)).toReal else 0) R) := by
  have hf : Measurable (fun p : K × ℝ≥0 ↦ (eCumulativeHazard (κ p.1) p.2).toReal) :=
    (measurable_eCumulativeHazard_kernel κ).ennreal_toReal
  have hf0 : ∀ z : K, (eCumulativeHazard (κ z) 0).toReal = 0 := by
    intro z
    rw [eCumulativeHazard_zero, ENNReal.toReal_zero]
  exact (hf.isStronglyPredictable_delayed_of_zero hL hZ z₀ hf0).stoppedProcess hR

/-- Ordered calendar lifetimes give the actual absorbing-gap representation
of the stopped delayed hazard, including infinite and coincident lifetimes.
This pointwise identity does not require either lifetime to be a stopping time. -/
theorem stoppedProcess_delayed_eCumulativeHazard_eq_gap
    (κ : Kernel K (WithTop ℝ≥0)) (Z : Ω → K)
    (hLR : ∀ ω, L ω ≤ R ω) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess
      (fun (s : ℝ≥0) v ↦ if L v ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ (Z v)) (s - (L v).untopA)).toReal else 0) R t ω =
      if L ω ≤ (t : WithTop ℝ≥0) then
        stoppedProcess (fun s (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ (Z ω)) s).toReal)
          id (t - (L ω).untopA) (if L ω = ⊤ then ⊤ else R ω - L ω)
      else 0 := by
  classical
  cases hLω : L ω with
  | top =>
      have hRω : R ω = ⊤ := top_unique (hLω ▸ hLR ω)
      simp only [stoppedProcess, hRω, min_eq_left le_top, WithTop.untopA,
        WithTop.untopD_coe, hLω, WithTop.not_top_le_coe, if_false]
  | coe l =>
      cases hRω : R ω with
      | top =>
          simp only [stoppedProcess, id_eq, hLω, hRω, WithTop.coe_ne_top, if_false,
            WithTop.top_sub_coe, min_eq_left le_top, WithTop.untopA,
            WithTop.untopD_coe]
      | coe r =>
          have hlr : l ≤ r := WithTop.coe_le_coe.mp (by
            simpa only [hLω, hRω] using hLR ω)
          have hclock : min t r - l = min (t - l) (r - l) := by
            by_cases htr : t ≤ r
            · rw [min_eq_left htr, min_eq_left (tsub_le_tsub_right htr l)]
            · have hrt := le_of_not_ge htr
              rw [min_eq_right hrt, min_eq_right (tsub_le_tsub_right hrt l)]
          simp only [stoppedProcess, id_eq, hLω, hRω, WithTop.coe_ne_top, if_false,
            ← WithTop.coe_sub, ← WithTop.coe_min, WithTop.untopA,
            WithTop.untopD_coe, WithTop.coe_le_coe]
          by_cases hlt : l ≤ t
          · rw [if_pos (le_min hlt hlr), if_pos hlt, hclock]
          · have hmin : ¬l ≤ min t r := fun h ↦ hlt (h.trans (min_le_left t r))
            rw [if_neg hmin, if_neg hlt]

end ProbabilityTheory
