/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.MeasureTheory.Integral.Indicator

/-! # Vanishing probabilities of early localization

AE divergence of a pre-localizing sequence already suffices. Monotonicity is not needed
for the probability estimate.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {τ : ℕ → Ω → WithTop ℝ≥0}

theorem tendsto_measure_le_of_ae_tendsto_top (hm : ∀ n, Measurable (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 ⊤))
    (T : ℝ≥0) : Tendsto (fun n ↦ P {ω | τ n ω ≤ T}) atTop (𝓝 0) := by
  have he : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ {ω | τ n ω ≤ T} ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hlim] with ω hω
    filter_upwards [hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with n hn
    simp only [mem_empty_iff_false, iff_false]
    exact not_le.mpr hn
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
      (fun n ↦ measurableSet_le (hm n) measurable_const) he

theorem IsPreLocalizingSequence.tendsto_measure_le (hτ : IsPreLocalizingSequence F τ P)
    (T : ℝ≥0) : Tendsto (fun n ↦ P {ω | τ n ω ≤ T}) atTop (𝓝 0) :=
  tendsto_measure_le_of_ae_tendsto_top
    (fun n ↦ (hτ.isStoppingTime n).measurable.mono (hτ.isStoppingTime n).measurableSpace_le le_rfl)
    hτ.tendsto_top T

end ProbabilityTheory
