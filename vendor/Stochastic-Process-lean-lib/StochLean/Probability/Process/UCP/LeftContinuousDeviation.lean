/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP
public import StochLean.Probability.Process.Path.Caglad

/-! # Compact deviations for left-continuous paths

The initial value is included separately from the dense grid. Left continuity
on a half-line imposes no relation between that value and its right limit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

theorem le_of_denseTimeUpTo_le_of_leftContinuous {E : Type*}
    [TopologicalSpace E] [Preorder E] [OrderClosedTopology E]
    {f : ℝ≥0 → E} (hf : IsLeftContinuousPath f) {T t : ℝ≥0} (ht : t ≤ T)
    {a : E} (hzero : f 0 ≤ a) (hbound : ∀ n, f (denseTimeUpTo T n) ≤ a) : f t ≤ a := by
  by_cases ht0 : t = 0
  · simpa only [ht0] using hzero
  have hdense : Dense (range (TopologicalSpace.denseSeq ℝ≥0)) :=
    TopologicalSpace.denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hdense.exists_seq_strictMono_tendsto_of_lt
    (pos_iff_ne_zero.mpr ht0)
  have hwithin : Tendsto u atTop (𝓝[≤] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1.2.le⟩
  apply le_of_tendsto' ((hf t).tendsto.comp hwithin)
  intro n
  obtain ⟨k, hk⟩ := (hu n).2
  have hclip : denseTimeUpTo T k = u n := by
    rw [denseTimeUpTo, hk, min_eq_right ((hu n).1.2.le.trans ht)]
  simpa only [hclip, Function.comp_apply] using hbound k

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem compactDeviation_eq_dense_of_leftContinuous {T : ℝ≥0} {ω : Ω}
    (hX : IsLeftContinuousPath (X · ω)) (hY : IsLeftContinuousPath (Y · ω)) :
    compactDeviation X Y T ω = max (ENNReal.ofReal ‖X 0 ω - Y 0 ω‖)
      (denseRunningSupremum (fun t ω ↦ ‖X t ω - Y t ω‖) T ω) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply le_of_denseTimeUpTo_le_of_leftContinuous
      (fun s ↦ ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (((hX s).sub (hY s)).norm)) ht (le_max_left _ _)
    intro n
    exact (le_iSup (fun n ↦ ENNReal.ofReal
      ‖X (denseTimeUpTo T n) ω - Y (denseTimeUpTo T n) ω‖) n).trans (le_max_right _ _)
  · apply max_le
    · exact enorm_sub_le_compactDeviation bot_le ω
    · apply iSup_le
      intro n
      exact enorm_sub_le_compactDeviation (min_le_left _ _) ω

theorem aemeasurable_compactDeviation_of_leftContinuous
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hrX : ∀ᵐ ω ∂P, IsLeftContinuousPath (X · ω))
    (hrY : ∀ᵐ ω ∂P, IsLeftContinuousPath (Y · ω)) (T : ℝ≥0) :
    AEMeasurable (compactDeviation X Y T) P := by
  have hm := ((ENNReal.measurable_ofReal.comp ((hX 0).sub (hY 0)).norm).max
    (measurable_denseRunningSupremum (fun t ↦ ((hX t).sub (hY t)).norm) T)).aemeasurable
      (μ := P)
  apply hm.congr
  filter_upwards [hrX, hrY] with ω hx hy
  exact (compactDeviation_eq_dense_of_leftContinuous hx hy).symm

end ProbabilityTheory
