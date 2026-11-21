/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TaggedStepApproximation
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Endpoint step convergence at jumps

On positive-time cells the left endpoint approaches strictly from below,
while the right endpoint approaches from above, allowing equality. Thus the
limits are different at jumps. No uniform convergence is asserted.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0} {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}

theorem tendsto_leftStep_of_tendsto_left {t : ℝ≥0} (ht : t ∈ Ioc 0 T) {l : ℝ}
    (hl : Tendsto f (𝓝[<] t) (𝓝 l))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).leftStep f t) atTop (𝓝 l) := by
  choose i hi using fun n ↦ (π n).exists_cell ht
  have hpoint : Tendsto (fun n ↦ (π n).left (i n)) atTop (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).1⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (π n).dist_left_of_mem_cell_le_mesh (hi n)
  simpa only [Function.comp_def, fun n ↦ (π n).leftStep_eq_of_mem_cell f (hi n)] using
    hl.comp hpoint

theorem tendsto_rightStep_of_continuousWithinAt {t : ℝ≥0} (ht : t ∈ Ioc 0 T)
    (hr : ContinuousWithinAt f (Ici t) t)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).taggedStep (π n).right f t) atTop (𝓝 (f t)) := by
  choose i hi using fun n ↦ (π n).exists_cell ht
  have hpoint : Tendsto (fun n ↦ (π n).right (i n)) atTop (𝓝[≥] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n ↦ (hi n).2⟩
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hmesh
    simpa only [dist_comm] using (π n).dist_tag_of_mem_cell_le_mesh (π n).right
      (fun j ↦ ⟨(π n).left_le_right j, le_rfl⟩) (hi n)
  simpa only [Function.comp_def,
    fun n ↦ (π n).taggedStep_eq_of_mem_cell (π n).right f (hi n)] using hr.tendsto.comp hpoint

theorem norm_taggedStep_le (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (hξ : ∀ i, ξ i ∈ Icc 0 T) {C : ℝ} (hb : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ C)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) : ‖π.taggedStep ξ f t‖ ≤ C := by
  by_cases ht0 : t = 0
  · subst t
    rw [taggedStep_zero]
    exact hb 0 ht
  · obtain ⟨i, hi⟩ := π.exists_cell ⟨pos_iff_ne_zero.mpr ht0, ht.2⟩
    rw [π.taggedStep_eq_of_mem_cell ξ f hi]
    exact hb (ξ i) (hξ i)

theorem measurable_taggedStep (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (f : ℝ≥0 → ℝ) : Measurable (π.taggedStep ξ f) := by
  classical
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc)

end StochLean.TimePartition
