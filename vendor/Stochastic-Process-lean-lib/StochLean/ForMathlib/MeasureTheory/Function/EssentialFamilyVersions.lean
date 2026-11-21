/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.EssentialFamilySupremum

/-! # Coherent representatives attaining a measurable family supremum

A selected countable subfamily defines a measurable bound `W`. Replacing each coordinate `f i`
by `min W (f i)` changes it only on its own null event. The selected coordinates are unchanged
pointwise, so the full, possibly uncountable, pointwise supremum of the new representatives is
exactly `W`. This is a construction of coherent versions, not a claim about arbitrary versions.
-/

@[expose] public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {f : ι → Ω → ℝ≥0∞}

/-- Capping every coordinate by a subfamily supremum leaves exactly that supremum as the full
pointwise supremum: every selected coordinate already lies below the cap. -/
theorem iSup_min_iSup_subtype_eq (f : ι → Ω → ℝ≥0∞) (I : Set ι) (ω : Ω) :
    (⨆ i : ι, min (⨆ j : I, f j.1 ω) (f i ω)) = ⨆ j : I, f j.1 ω := by
  apply le_antisymm (iSup_le fun _ ↦ min_le_left _ _)
  apply iSup_le
  intro j
  have hj : f j.1 ω ≤ ⨆ k : I, f k.1 ω := le_iSup (fun k : I ↦ f k.1 ω) j
  calc
    f j.1 ω = min (⨆ k : I, f k.1 ω) (f j.1 ω) := (min_eq_right hj).symm
    _ ≤ ⨆ i : ι, min (⨆ k : I, f k.1 ω) (f i ω) :=
      le_iSup (fun i : ι ↦ min (⨆ k : I, f k.1 ω) (f i ω)) j.1

/-- A measurable family admits coherent measurable versions whose full pointwise supremum is
a measurable essential supremum. The versions are actual pointwise downward truncations and
agree with their respective original coordinates almost surely. Empty families are allowed. -/
theorem exists_coherent_aeFamilySupremum (μ : Measure Ω) [SFinite μ]
    (hf : ∀ i : ι, Measurable (f i)) :
    ∃ (W : Ω → ℝ≥0∞) (g : ι → Ω → ℝ≥0∞), IsAEFamilySupremum μ f W ∧
      (∀ i : ι, Measurable (g i)) ∧ (∀ i : ι, g i =ᵐ[μ] f i) ∧
        (∀ ω, (⨆ i : ι, g i ω) = W ω) ∧ (∀ i ω, g i ω ≤ f i ω) := by
  obtain ⟨I, hI, hdom⟩ := μ.exists_countable_subfamily_ae_le_iSup hf
  let W : Ω → ℝ≥0∞ := fun ω ↦ ⨆ j : I, f j.1 ω
  let g : ι → Ω → ℝ≥0∞ := fun i ω ↦ min (W ω) (f i ω)
  have hW : IsAEFamilySupremum μ f W := isAEFamilySupremum_iSup_subtype hf hI hdom
  refine ⟨W, g, hW, fun i ↦ hW.measurable.min (hf i), ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hW.le_ae i] with ω hω
    exact min_eq_right hω
  · exact fun ω ↦ iSup_min_iSup_subtype_eq f I ω
  · exact fun _ _ ↦ min_le_right _ _

/-- The literal full pointwise supremum is measurable and is an essential supremum after
choosing the coherent versions above. Each coordinate retains its original almost-sure class. -/
theorem exists_measurable_iSup_ae_versions (μ : Measure Ω) [SFinite μ]
    (hf : ∀ i : ι, Measurable (f i)) :
    ∃ g : ι → Ω → ℝ≥0∞, (∀ i : ι, Measurable (g i)) ∧
      (∀ i : ι, g i =ᵐ[μ] f i) ∧ Measurable (fun ω ↦ ⨆ i : ι, g i ω) ∧
        IsAEFamilySupremum μ f (fun ω ↦ ⨆ i : ι, g i ω) := by
  obtain ⟨W, g, hW, hgm, hgf, he, _⟩ := exists_coherent_aeFamilySupremum μ hf
  have hfun : (fun ω ↦ ⨆ i : ι, g i ω) = W := funext he
  refine ⟨g, hgm, hgf, ?_, ?_⟩
  · rw [hfun]
    exact hW.measurable
  · rw [hfun]
    exact hW

end MeasureTheory
