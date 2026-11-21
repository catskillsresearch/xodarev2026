/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilyVersions
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Regression: coordinate null events cannot be intersected uncountably

Singleton spikes are individually zero almost surely for a measure giving zero mass to every
singleton, yet their full pointwise supremum is one at every sample. Their essential supremum
is zero. Thus even measurable raw coordinate representatives cannot in general be used to form
the source full supremum without a coherent-version construction.
-/

@[expose] public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory.EssentialFamilyRegression

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A separate null spike for each index in the sample space. -/
noncomputable def singletonSpikeFamily (i : Ω) : Ω → ℝ≥0∞ :=
  ({i} : Set Ω).indicator (fun _ ↦ 1)

theorem measurable_singletonSpikeFamily [MeasurableSingletonClass Ω] (i : Ω) :
    Measurable (singletonSpikeFamily i) :=
  measurable_const.indicator (measurableSet_singleton i)

theorem singletonSpikeFamily_ae_eq_zero (μ : Measure Ω) [NullSingletonClass μ] (i : Ω) :
    singletonSpikeFamily i =ᵐ[μ] (fun _ ↦ 0) := by
  filter_upwards [μ.ae_ne i] with ω hω
  exact indicator_of_notMem (show ω ∉ ({i} : Set Ω) from hω) _

/-- The raw pointwise supremum sees the exceptional spike indexed by the current sample. -/
theorem iSup_singletonSpikeFamily (ω : Ω) : (⨆ i : Ω, singletonSpikeFamily i ω) = 1 := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro i
    by_cases hω : ω = i
    · simp only [singletonSpikeFamily, indicator_apply, mem_singleton_iff, hω, if_true, le_refl]
    · simp only [singletonSpikeFamily, indicator_apply, mem_singleton_iff, hω, if_false,
        zero_le]
  · have hself : singletonSpikeFamily ω ω = 1 := by
      simp only [singletonSpikeFamily, indicator_of_mem (mem_singleton ω)]
    rw [← hself]
    exact le_iSup (fun i : Ω ↦ singletonSpikeFamily i ω) ω

/-- The essential supremum ignores the separate singleton null spikes. -/
theorem isAEFamilySupremum_singletonSpikeFamily_zero (μ : Measure Ω)
    [NullSingletonClass μ] :
    IsAEFamilySupremum μ singletonSpikeFamily (fun _ ↦ 0) := by
  refine ⟨measurable_const, fun i ↦ ?_, fun U _ ↦ ?_⟩
  · exact (singletonSpikeFamily_ae_eq_zero μ i).mono fun _ he ↦ he.le
  · exact Eventually.of_forall fun _ ↦ bot_le

/-- On a nonzero singleton-null measure, the raw full supremum is not an essential supremum,
despite every coordinate having zero almost-sure class. -/
theorem not_isAEFamilySupremum_singletonSpikeFamily_iSup (μ : Measure Ω)
    [NullSingletonClass μ] [NeZero μ] :
    ¬ IsAEFamilySupremum μ singletonSpikeFamily
      (fun ω ↦ ⨆ i : Ω, singletonSpikeFamily i ω) := by
  intro h
  have he := h.ae_eq (isAEFamilySupremum_singletonSpikeFamily_zero μ)
  obtain ⟨ω, hω⟩ := he.exists
  exact one_ne_zero (by simpa only [iSup_singletonSpikeFamily] using hω)

end MeasureTheory.EssentialFamilyRegression
