/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.Predictable
public import StochLean.Probability.Process.Path.Step

/-! # The Protter and Mathlib predictable sigma-fields agree

The right-hand side is the smallest sigma-field making all everywhere-caglad
adapted real processes measurable. The theorem identifies it with Mathlib's
existing rectangle-generated predictable sigma-field; no second owner is defined.
Almost-sure path properties must first use the indistinguishable-version bridge.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem predictable_eq_iSup_comap_caglad (F : Filtration ℝ≥0 mΩ) :
    F.predictable = ⨆ (X : ℝ≥0 → Ω → ℝ) (_ : Adapted F X)
      (_ : ∀ ω, IsCagladPath (fun t ↦ X t ω)),
      MeasurableSpace.comap (Function.uncurry X) inferInstance := by
  classical
  let C := ⨆ (X : ℝ≥0 → Ω → ℝ) (_ : Adapted F X)
      (_ : ∀ ω, IsCagladPath (fun t ↦ X t ω)),
      MeasurableSpace.comap (Function.uncurry X) inferInstance
  change F.predictable = C
  have hgen (X : ℝ≥0 → Ω → ℝ) (ha : Adapted F X)
      (hc : ∀ ω, IsCagladPath (fun t ↦ X t ω)) :
      Measurable[C] (Function.uncurry X) :=
    measurable_iff_comap_le.mpr
      (le_iSup_of_le X (le_iSup_of_le ha (le_iSup_of_le hc le_rfl)))
  apply le_antisymm
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ if t = 0 then A.indicator (fun _ ↦ 1) ω else 0
      have ha : Adapted F X := by
        intro t
        by_cases ht : t = 0
        · subst t
          simp only [X]
          exact measurable_const.indicator hA
        · simp only [X, if_neg ht]
          exact measurable_const
      have hc : ∀ ω, IsCagladPath (fun t ↦ X t ω) := by
        intro ω
        exact isCagladPath_initialSpike (A.indicator (fun _ ↦ 1) ω)
      have hm := hgen X ha hc (measurableSet_singleton (1 : ℝ))
      convert hm using 1
      ext ⟨t, ω⟩
      by_cases ht : t = 0 <;> by_cases hω : ω ∈ A <;> simp [X, ht, hω]
    · intro a A hA
      let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ if a < t then A.indicator (fun _ ↦ 1) ω else 0
      have ha : Adapted F X := by
        intro t
        by_cases ht : a < t
        · simp only [X, if_pos ht]
          exact measurable_const.indicator (F.mono ht.le _ hA)
        · simp only [X, if_neg ht]
          exact measurable_const
      have hc : ∀ ω, IsCagladPath (fun t ↦ X t ω) := by
        intro ω
        exact isCagladPath_step_Ioi a (A.indicator (fun _ ↦ 1) ω)
      have hm := hgen X ha hc (measurableSet_singleton (1 : ℝ))
      convert hm using 1
      ext ⟨t, ω⟩
      by_cases ht : a < t <;> by_cases hω : ω ∈ A <;> simp [X, ht, hω]
  · apply iSup_le
    intro X
    apply iSup_le
    intro ha
    apply iSup_le
    intro hc
    exact (ha.isStronglyPredictable_of_leftContinuous (fun ω ↦ (hc ω).1)).measurable.comap_le

end MeasureTheory.Filtration
