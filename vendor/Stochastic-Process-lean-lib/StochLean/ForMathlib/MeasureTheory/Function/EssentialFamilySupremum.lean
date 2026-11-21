/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Bases

/-! # Measurable essential suprema of arbitrarily indexed families

The relation is specified before proving existence. It is an almost-sure upper bound of each
coordinate and is below every other almost-sure upper bound, including a nonmeasurable bound.
It is not the pointwise supremum over an uncountable family of chosen representatives.

For an s-finite measure, countable essential unions of strict threshold events select a
countable subfamily with the same essential supremum. For each fixed original index, only the
countable dense threshold family is intersected almost surely. The empty index type is allowed
and gives zero. No global representative selector is introduced.
-/

@[expose] public section

open Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-- A measurable essential supremum of a family of extended nonnegative random variables.
The comparison function in the least-upper-bound property need not be measurable. -/
structure IsAEFamilySupremum (μ : Measure Ω) (f : ι → Ω → ℝ≥0∞)
    (W : Ω → ℝ≥0∞) : Prop where
  measurable : Measurable W
  le_ae : ∀ i : ι, f i ≤ᵐ[μ] W
  ae_le : ∀ g : Ω → ℝ≥0∞, (∀ i : ι, f i ≤ᵐ[μ] g) → W ≤ᵐ[μ] g

variable {μ : Measure Ω} {f g : ι → Ω → ℝ≥0∞} {W V : Ω → ℝ≥0∞}

/-- Essential family suprema are unique up to almost-sure equality. -/
theorem IsAEFamilySupremum.ae_eq (hW : IsAEFamilySupremum μ f W)
    (hV : IsAEFamilySupremum μ f V) : W =ᵐ[μ] V := by
  filter_upwards [hW.ae_le V hV.le_ae, hV.ae_le W hW.le_ae] with ω hw hv
  exact le_antisymm hw hv

/-- Changing every coordinate on its own null event leaves the essential-supremum relation
unchanged. No common exceptional event for all original indices is required. -/
theorem IsAEFamilySupremum.congr_family (hW : IsAEFamilySupremum μ f W)
    (hfg : ∀ i : ι, f i =ᵐ[μ] g i) : IsAEFamilySupremum μ g W := by
  refine ⟨hW.measurable, fun i ↦ ?_, fun U hU ↦ ?_⟩
  · filter_upwards [hfg i, hW.le_ae i] with ω he hw
    exact he.symm.trans_le hw
  · apply hW.ae_le U
    intro i
    filter_upwards [hfg i, hU i] with ω he hu
    exact he.trans_le hu

/-- An empty family has essential supremum zero, for every measure. -/
theorem isAEFamilySupremum_zero_of_isEmpty [IsEmpty ι] :
    IsAEFamilySupremum μ f (fun _ ↦ 0) := by
  refine ⟨measurable_const, fun i ↦ isEmptyElim i, fun U _ ↦ ?_⟩
  exact Eventually.of_forall fun _ ↦ bot_le

/-- An s-finite measure permits a countable subfamily whose ordinary countable supremum
dominates each original coordinate almost surely. The set of selected indices may be empty. -/
theorem Measure.exists_countable_subfamily_ae_le_iSup (μ : Measure Ω) [SFinite μ]
    (hf : ∀ i : ι, Measurable (f i)) :
    ∃ I : Set ι, I.Countable ∧ ∀ i : ι,
      f i ≤ᵐ[μ] (fun ω ↦ ⨆ j : I, f j.1 ω) := by
  classical
  let q : ℕ → ℝ≥0∞ := denseSeq ℝ≥0∞
  have hselect (n : ℕ) :
      ∃ D ⊆ range (fun i : ι ↦ {ω | q n < f i ω}), D.Countable ∧
        ∀ i : ι, {ω | q n < f i ω} ≤ᵐ[μ] (⋃₀ D) := by
    obtain ⟨D, hDC, hDcount, hD⟩ := μ.exists_ae_subset_biUnion_countable
      (C := range (fun i : ι ↦ {ω | q n < f i ω})) (by
        rintro A ⟨i, rfl⟩
        exact measurableSet_lt measurable_const (hf i))
    exact ⟨D, hDC, hDcount, fun i ↦ hD _ ⟨i, rfl⟩⟩
  choose D hDC hDcount hD using hselect
  let κ := Σ n : ℕ, D n
  let : ∀ n : ℕ, Countable (D n) := fun n ↦ (hDcount n).to_subtype
  have horigin (k : κ) : ∃ i : ι, {ω | q k.1 < f i ω} = k.2.1 :=
    hDC k.1 k.2.2
  choose a ha using horigin
  let I : Set ι := range a
  have hI : I.Countable := countable_range a
  refine ⟨I, hI, fun i ↦ ?_⟩
  have hthreshold (n : ℕ) : ∀ᵐ ω ∂μ, q n < f i ω → ω ∈ ⋃₀ D n := hD n i
  filter_upwards [ae_all_iff.mpr hthreshold] with ω hω
  by_contra hnot
  have hlt : (⨆ j : I, f j.1 ω) < f i ω := lt_of_not_ge hnot
  obtain ⟨r, ⟨n, rfl⟩, hWr, hrf⟩ := (denseRange_denseSeq ℝ≥0∞).exists_between hlt
  have hmem : ω ∈ ⋃₀ D n := hω n hrf
  obtain ⟨A, hAD, hωA⟩ := hmem
  let k : κ := ⟨n, ⟨A, hAD⟩⟩
  let j : I := ⟨a k, mem_range_self k⟩
  have hqa : q n < f (a k) ω := by
    change ω ∈ {ω | q k.1 < f (a k) ω}
    rw [ha k]
    exact hωA
  have hle : f (a k) ω ≤ ⨆ j : I, f j.1 ω := le_iSup (fun j : I ↦ f j.1 ω) j
  exact (not_lt_of_ge hle) (hWr.trans hqa)

/-- A dominating countable subfamily produces the measurable essential-supremum relation.
Minimality uses only a countable almost-sure intersection, even for a nonmeasurable bound. -/
theorem isAEFamilySupremum_iSup_subtype (hf : ∀ i : ι, Measurable (f i))
    {I : Set ι} (hI : I.Countable)
    (hdom : ∀ i : ι, f i ≤ᵐ[μ] (fun ω ↦ ⨆ j : I, f j.1 ω)) :
    IsAEFamilySupremum μ f (fun ω ↦ ⨆ j : I, f j.1 ω) := by
  let : Countable I := hI.to_subtype
  refine ⟨Measurable.iSup (fun j : I ↦ hf j.1), hdom, fun U hU ↦ ?_⟩
  have hcount : ∀ᵐ ω ∂μ, ∀ j : I, f j.1 ω ≤ U ω :=
    ae_all_iff.mpr (fun j : I ↦ hU j.1)
  filter_upwards [hcount] with ω hω
  exact iSup_le hω

/-- Every measurable extended-nonnegative family has a measurable essential supremum for an
s-finite measure. Existence precedes any possible downstream choice of a representative. -/
theorem exists_isAEFamilySupremum (μ : Measure Ω) [SFinite μ]
    (hf : ∀ i : ι, Measurable (f i)) : ∃ W : Ω → ℝ≥0∞, IsAEFamilySupremum μ f W := by
  obtain ⟨I, hI, hdom⟩ := μ.exists_countable_subfamily_ae_le_iSup hf
  exact ⟨fun ω ↦ ⨆ j : I, f j.1 ω, isAEFamilySupremum_iSup_subtype hf hI hdom⟩

end MeasureTheory
