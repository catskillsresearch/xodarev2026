/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map

/-! # Actual finite lifetime windows in real coordinates

Absolute continuity of the actual finite-coordinate pushforward rules out
an atom at infinity: its image is a real singleton of Lebesgue measure
zero. This argument does not interpret the totalized value at infinity as
a finite lifetime and does not depend on which real value it takes.

Once infinity has zero mass, real half-open windows agree with the actual
extended-lifetime windows on the common finite-lifetime event. Zero
endpoints and arbitrarily ordered endpoints are included. No probability
or finite-measure hypothesis, and no alternate lifetime owner, is used.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- A Lebesgue-absolutely-continuous real finite-coordinate law has no
original mass at infinity, since the entire infinite atom maps to a null
real singleton. No finiteness of the original law is needed. -/
theorem measure_top_eq_zero_of_absolutelyContinuous_map_untopA
    (μ : Measure (WithTop ℝ≥0))
    (hAC : μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ)) ≪ volume) :
    μ {⊤} = 0 := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hzero : μ (φ ⁻¹' {φ ⊤}) = 0 := by
    rw [← Measure.map_apply hφ (measurableSet_singleton (φ ⊤))]
    exact hAC (measure_singleton (φ ⊤))
  apply measure_mono_null ?_ hzero
  intro v hv
  rcases mem_singleton_iff.mp hv with rfl
  rfl

/-- In the absence of infinite mass, every actual real half-open lifetime
window is the corresponding extended-lifetime window, including zero
endpoints and empty windows. -/
theorem map_untopA_real_Ico (μ : Measure (WithTop ℝ≥0))
    (hTop : μ {⊤} = 0) (t u : ℝ≥0) :
    (μ.map (fun v : WithTop ℝ≥0 ↦ (v.untopA : ℝ))) (Ico (t : ℝ) (u : ℝ)) =
      μ (Ico (t : WithTop ℝ≥0) (u : WithTop ℝ≥0)) := by
  let φ : WithTop ℝ≥0 → ℝ := fun v ↦ (v.untopA : ℝ)
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp measurable_id.untopA
  have hfinite : ∀ᵐ v ∂μ, v ≠ ⊤ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hTop
  rw [Measure.map_apply hφ measurableSet_Ico]
  apply measure_congr
  filter_upwards [hfinite] with v hv
  cases v using WithTop.recTopCoe with
  | top => exact (hv rfl).elim
  | coe a =>
      apply propext
      change ((t : ℝ) ≤ (a : ℝ) ∧ (a : ℝ) < (u : ℝ)) ↔
        ((t : WithTop ℝ≥0) ≤ (a : WithTop ℝ≥0) ∧
          (a : WithTop ℝ≥0) < (u : WithTop ℝ≥0))
      simp only [NNReal.coe_le_coe, NNReal.coe_lt_coe,
        WithTop.coe_le_coe, WithTop.coe_lt_coe]

end ProbabilityTheory
