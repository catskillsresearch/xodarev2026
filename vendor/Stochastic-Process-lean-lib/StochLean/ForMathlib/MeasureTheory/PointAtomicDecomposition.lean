/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # The point-atomic and point-diffuse parts of an s-finite measure

The countable set of positive-mass singletons is intrinsic. Restriction to it
and to its complement gives the decomposition. On general measurable spaces,
having no point atoms is not asserted to exclude all nonsingleton atoms.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]

def pointAtomSet (μ : Measure T) : Set T := {t | μ {t} ≠ 0}

theorem countable_pointAtomSet (μ : Measure T) [SFinite μ] : (pointAtomSet μ).Countable := by
  simpa only [pointAtomSet, pos_iff_ne_zero] using
    (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
      (fun t : T ↦ measurableSet_singleton t)
      (fun _ _ h ↦ disjoint_singleton.mpr h))

noncomputable def pointAtomicPart (μ : Measure T) : Measure T := μ.restrict (pointAtomSet μ)

noncomputable def pointDiffusePart (μ : Measure T) : Measure T := μ.restrict (pointAtomSet μ)ᶜ

theorem pointAtomicPart_add_pointDiffusePart (μ : Measure T) [SFinite μ] :
    pointAtomicPart μ + pointDiffusePart μ = μ :=
  Measure.restrict_add_restrict_compl (countable_pointAtomSet μ).measurableSet

omit [MeasurableSingletonClass T] in
theorem pointAtomicPart_le (μ : Measure T) : pointAtomicPart μ ≤ μ := Measure.restrict_le_self

omit [MeasurableSingletonClass T] in
theorem pointDiffusePart_le (μ : Measure T) : pointDiffusePart μ ≤ μ := Measure.restrict_le_self

theorem pointAtomicPart_singleton (μ : Measure T) (t : T) : pointAtomicPart μ {t} = μ {t} := by
  classical
  rw [pointAtomicPart, Measure.restrict_apply (measurableSet_singleton t)]
  by_cases ht : t ∈ pointAtomSet μ
  · rw [inter_eq_left.mpr (singleton_subset_iff.mpr ht)]
  · have hz : μ {t} = 0 := not_not.mp ht
    rw [singleton_inter_eq_empty.mpr ht, measure_empty, hz]

instance pointDiffusePart_nullSingletonClass (μ : Measure T) :
    NullSingletonClass (pointDiffusePart μ) := by
  classical
  refine ⟨fun t ↦ ?_⟩
  rw [pointDiffusePart, Measure.restrict_apply (measurableSet_singleton t)]
  by_cases ht : t ∈ pointAtomSet μ
  · rw [singleton_inter_eq_empty.mpr (show t ∉ (pointAtomSet μ)ᶜ from fun hc ↦ hc ht),
      measure_empty]
  · rw [inter_eq_left.mpr (singleton_subset_iff.mpr ht)]
    exact not_not.mp ht

theorem pointAtomicPart_apply (μ : Measure T) [SFinite μ] {s : Set T} (hs : MeasurableSet s) :
    pointAtomicPart μ s = ∑' t : ↥(s ∩ pointAtomSet μ), μ {(t : T)} := by
  rw [pointAtomicPart, Measure.restrict_apply hs]
  have hc : (s ∩ pointAtomSet μ).Countable := (countable_pointAtomSet μ).mono inter_subset_right
  simpa only [preimage_id] using
    (tsum_measure_preimage_singleton (μ := μ) hc (f := id)
      (fun t _ ↦ measurableSet_singleton t)).symm

theorem pointAtomicPart_apply_eq_tsum (μ : Measure T) [SFinite μ]
    {s : Set T} (hs : MeasurableSet s) :
    pointAtomicPart μ s = ∑' t : s, μ {(t : T)} := by
  classical
  have hsupport : Function.support (s.indicator fun t ↦ μ {t}) ⊆ s ∩ pointAtomSet μ := by
    intro t ht
    have hmem : t ∈ s := by
      by_contra h
      exact ht (indicator_of_notMem h _)
    refine ⟨hmem, ?_⟩
    simpa only [pointAtomSet, mem_ofPred_eq, Function.mem_support, indicator_of_mem hmem] using ht
  calc
    _ = ∑' t : ↥(s ∩ pointAtomSet μ), μ {(t : T)} := pointAtomicPart_apply μ hs
    _ = ∑' t : ↥(s ∩ pointAtomSet μ), s.indicator (fun u ↦ μ {u}) t := by
      apply tsum_congr
      intro t
      rw [indicator_of_mem t.2.1]
    _ = ∑' t, s.indicator (fun u ↦ μ {u}) t := tsum_subtype_eq_of_support_subset hsupport
    _ = ∑' t : s, μ {(t : T)} := (tsum_subtype s (fun t ↦ μ {t})).symm

end StochLean
