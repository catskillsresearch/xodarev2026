/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Coefficient

/-! # Revealing source coefficients at another stopping time -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- A coefficient known at `τ` can be revealed at `σ` on the event `τ ≤ σ`.
No right-continuity or completeness assumption is needed. -/
theorem measurable_indicator_le_stopping (τ σ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) :
    Measurable[σ.measurableSpace] (fun ω ↦ if τ ω ≤ σ ω then Z ω else 0) := by
  classical
  have hle : MeasurableSet[σ.measurableSpace] {ω | τ ω ≤ σ ω} := by
    simpa only [WithTop.coe_le_coe] using
      τ.isStoppingTime.measurableSet_stopping_time_le σ.isStoppingTime
  have hpre : ∀ s, MeasurableSet s →
      MeasurableSet[σ.measurableSpace] (Z ⁻¹' s ∩ {ω | τ ω ≤ σ ω}) := by
    intro s hs
    have h := τ.isStoppingTime.measurableSet_inter_le σ.isStoppingTime _ (hZ hs)
    rw [IsStoppingTime.measurableSet_min_iff τ.isStoppingTime σ.isStoppingTime] at h
    simpa only [WithTop.coe_le_coe] using h.2
  intro s hs
  by_cases h0 : (0 : ℝ) ∈ s
  · have heq : (fun ω ↦ if τ ω ≤ σ ω then Z ω else 0) ⁻¹' s =
        (Z ⁻¹' s ∩ {ω | τ ω ≤ σ ω}) ∪ {ω | τ ω ≤ σ ω}ᶜ := by
      ext ω
      by_cases h : τ ω ≤ σ ω <;> simp [h, h0]
    rw [heq]
    exact (hpre s hs).union hle.compl
  · have heq : (fun ω ↦ if τ ω ≤ σ ω then Z ω else 0) ⁻¹' s =
        Z ⁻¹' s ∩ {ω | τ ω ≤ σ ω} := by
      ext ω
      by_cases h : τ ω ≤ σ ω <;> simp [h, h0]
    rw [heq]
    exact hpre s hs

/-- The value immediately after `σ` of a source coefficient on `(τ, υ]` is known at `σ`. -/
theorem measurable_right_interval_coefficient (τ υ σ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) :
    Measurable[σ.measurableSpace]
      (fun ω ↦ if τ ω ≤ σ ω ∧ σ ω < υ ω then Z ω else 0) := by
  classical
  have hlt : MeasurableSet[σ.measurableSpace] {ω | σ ω < υ ω} := by
    simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using
      (υ.isStoppingTime.measurableSet_stopping_time_le σ.isStoppingTime).compl
  have h : Measurable[σ.measurableSpace]
      (fun ω ↦ if σ ω < υ ω then (if τ ω ≤ σ ω then Z ω else 0) else 0) :=
    Measurable.ite hlt (τ.measurable_indicator_le_stopping σ hZ) measurable_const
  convert h using 1
  funext ω
  split_ifs <;> tauto

end ProbabilityTheory.FiniteStoppingTime
