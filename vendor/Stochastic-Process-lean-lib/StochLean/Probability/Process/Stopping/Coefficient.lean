/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Finite

/-! # Revealing a stopping-time coefficient strictly after its stopping time -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem measurable_indicator_lt (τ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) (t : ℝ≥0) :
    Measurable[F t] (fun ω ↦ if τ ω < t then Z ω else 0) := by
  classical
  have hlt : MeasurableSet[F t] {ω | τ ω < t} := by
    simpa only [WithTop.coe_lt_coe] using τ.isStoppingTime.measurableSet_lt t
  have hpre : ∀ s, MeasurableSet s → MeasurableSet[F t] (Z ⁻¹' s ∩ {ω | τ ω < t}) := by
    intro s hs
    have hle : MeasurableSet[F t] (Z ⁻¹' s ∩ {ω | τ ω ≤ t}) := by
      simpa only [WithTop.coe_le_coe] using
        ((τ.isStoppingTime.measurableSet _).mp (hZ hs)).2 t
    have heq : (Z ⁻¹' s ∩ {ω | τ ω ≤ t}) ∩ {ω | τ ω < t} =
        Z ⁻¹' s ∩ {ω | τ ω < t} := by
      ext ω
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · exact fun h ↦ ⟨⟨h.1, (show τ ω < t from h.2).le⟩, h.2⟩
    rw [← heq]
    exact hle.inter hlt
  intro s hs
  by_cases h0 : (0 : ℝ) ∈ s
  · have heq : (fun ω ↦ if τ ω < t then Z ω else 0) ⁻¹' s =
        (Z ⁻¹' s ∩ {ω | τ ω < t}) ∪ {ω | τ ω < t}ᶜ := by
      ext ω
      by_cases h : τ ω < t <;> simp [h, h0]
    rw [heq]
    exact (hpre s hs).union hlt.compl
  · have heq : (fun ω ↦ if τ ω < t then Z ω else 0) ⁻¹' s =
        Z ⁻¹' s ∩ {ω | τ ω < t} := by
      ext ω
      by_cases h : τ ω < t <;> simp [h, h0]
    rw [heq]
    exact hpre s hs

theorem measurable_interval_coefficient (τ σ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) (t : ℝ≥0) :
    Measurable[F t] (fun ω ↦ if τ ω < t ∧ t ≤ σ ω then Z ω else 0) := by
  classical
  have hge : MeasurableSet[F t] {ω | t ≤ σ ω} := by
    simpa only [WithTop.coe_le_coe] using σ.isStoppingTime.measurableSet_ge t
  have h : Measurable[F t]
      (fun ω ↦ if t ≤ σ ω then (if τ ω < t then Z ω else 0) else 0) :=
    Measurable.ite hge (τ.measurable_indicator_lt hZ t) measurable_const
  convert h using 1
  funext ω
  split_ifs <;> tauto

end ProbabilityTheory.FiniteStoppingTime
