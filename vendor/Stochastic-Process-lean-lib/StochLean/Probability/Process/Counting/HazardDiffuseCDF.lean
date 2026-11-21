/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardCDF
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Continuous lifetime CDFs without singleton masses

The actual real pushforward of a lifetime law with zero singleton masses
also has zero singleton masses. The totalized finite-coordinate map is not
claimed to be injective: each fiber becomes subsingleton only after the
infinite point is removed, and that point has zero original mass.

The original CDF is continuous because its Stieltjes singleton masses are
zero and its right continuity is already part of the native CDF owner.
The pre-jump survival identity can consequently use the current CDF value
instead of its strict left limit. Zero and infinite lifetime masses vanish
by the actual `NullSingletonClass` assumption; no density or absolute
continuity of the lifetime law is required.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

private theorem nullSingletonClass_map_real_lifetime
    (μ : Measure (WithTop ℝ≥0)) [NullSingletonClass μ] :
    NullSingletonClass (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))) := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  constructor
  intro x
  change μ.map φ {x} = 0
  rw [Measure.map_apply hφ (measurableSet_singleton x)]
  have hfiber : (φ ⁻¹' {x} \ ({⊤} : Set (WithTop ℝ≥0))).Subsingleton := by
    intro a ha b hb
    cases a using WithTop.recTopCoe with
    | top => exact (ha.2 rfl).elim
    | coe a =>
        cases b using WithTop.recTopCoe with
        | top => exact (hb.2 rfl).elim
        | coe b =>
            have ha' : (a : ℝ) = x := ha.1
            have hb' : (b : ℝ) = x := hb.1
            have hab : a = b := NNReal.coe_injective (ha'.trans hb'.symm)
            exact congrArg (fun z : ℝ≥0 ↦ (z : WithTop ℝ≥0)) hab
  have he : φ ⁻¹' {x} =ᵐ[μ] φ ⁻¹' {x} \ ({⊤} : Set (WithTop ℝ≥0)) := by
    filter_upwards [μ.ae_ne (⊤ : WithTop ℝ≥0)] with v hv
    apply propext
    change φ v = x ↔ φ v = x ∧ v ≠ ⊤
    exact (and_iff_left hv).symm
  exact (measure_congr he).trans (hfiber.measure_zero μ)

variable (μ : Measure (WithTop ℝ≥0)) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- A lifetime law without singleton masses gives a continuous native CDF
of its actual real pushforward, without assuming an absolutely continuous law. -/
theorem continuous_cdf_map_untopA :
    Continuous (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))) := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  let ν := μ.map φ
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  let : NullSingletonClass ν := nullSingletonClass_map_real_lifetime μ
  change Continuous (cdf ν)
  apply continuous_iff_continuousAt.mpr
  intro x
  have hm := (cdf ν).measure_singleton x
  rw [measure_cdf ν, measure_singleton] at hm
  have hle : cdf ν x ≤ Function.leftLim (cdf ν) x :=
    sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hm.symm)
  have hl : Function.leftLim (cdf ν) x = cdf ν x :=
    le_antisymm ((monotone_cdf ν).leftLim_le le_rfl) hle
  have hr : Function.rightLim (cdf ν) x = cdf ν x := ((cdf ν).right_continuous x).rightLim_eq
  exact (monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim.mpr (hl.trans hr.symm)

/-- For a lifetime law without singleton masses, pre-jump survival is
one minus the current native CDF. The zero and infinite lifetime atoms
are excluded by the singleton hypothesis, not by additional assumptions. -/
theorem one_sub_cdf_map_untopA_eq_survival (u : ℝ≥0) :
    1 - cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))) (u : ℝ) =
      μ.real (Ici (u : WithTop ℝ≥0)) := by
  have h := one_sub_leftLim_cdf_map_untopA_eq_survival μ (measure_singleton ⊤) u
  have hc : ContinuousWithinAt
      (cdf (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)))) (Iic (u : ℝ)) (u : ℝ) :=
    (continuous_cdf_map_untopA μ).continuousWithinAt
  rw [hc.leftLim_eq] at h
  exact h

end ProbabilityTheory
