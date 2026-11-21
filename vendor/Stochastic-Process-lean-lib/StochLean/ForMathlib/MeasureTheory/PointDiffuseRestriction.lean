/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.PointAtomicDecomposition

/-! # Point-diffuse restriction depends only on the restricted measure -/

@[expose] public section

open MeasureTheory Set

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]

theorem pointAtomSet_restrict (μ : Measure T) (s : Set T) :
    pointAtomSet (μ.restrict s) = s ∩ pointAtomSet μ := by
  classical
  ext t
  change (μ.restrict s) {t} ≠ 0 ↔ t ∈ s ∧ μ {t} ≠ 0
  rw [Measure.restrict_apply (measurableSet_singleton t)]
  by_cases ht : t ∈ s
  · rw [inter_eq_left.mpr (singleton_subset_iff.mpr ht)]
    simp only [ht, true_and]
  · rw [singleton_inter_eq_empty.mpr ht, measure_empty]
    simp only [ht, false_and, ne_eq, not_true_eq_false]

theorem pointDiffusePart_restrict (μ : Measure T) {s : Set T} (hs : MeasurableSet s) :
    pointDiffusePart (μ.restrict s) = (pointDiffusePart μ).restrict s := by
  rw [pointDiffusePart, pointAtomSet_restrict, Measure.restrict_restrict' hs,
    pointDiffusePart, Measure.restrict_restrict hs]
  congr 1
  ext t
  simp only [mem_inter_iff, mem_compl_iff]
  tauto

end StochLean
