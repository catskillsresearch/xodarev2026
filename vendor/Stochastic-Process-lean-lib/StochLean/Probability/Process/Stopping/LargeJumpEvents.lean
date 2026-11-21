/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.CadlagLargeJumpDetection
public import Mathlib.Probability.Process.Adapted

/-! # Measurable occurrence of a large cadlag jump

Only adapted coordinates at times below the fixed right endpoint are used.
The deterministic dense-increment characterization replaces an uncountable
projection by countable unions and intersections. Everywhere cadlag paths
suffice; neither completeness nor right continuity of the filtration is
required for these fixed-horizon occurrence events.
-/

@[expose] public section

open ProbabilityTheory Set TopologicalSpace
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

theorem Adapted.measurableSet_arbitrarilyShortDenseIncrements (hX : Adapted F X)
    (a d t : ℝ≥0) (hdt : d ≤ t) (c : ℝ) :
    MeasurableSet[F t] {ω | HasArbitrarilyShortDenseIncrements (X · ω) a d c} := by
  classical
  let : MeasurableSpace Ω := F t
  unfold HasArbitrarilyShortDenseIncrements
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  simp_rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hC : a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧
      denseSeq ℝ≥0 j ≤ d ∧
        dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ)
  · have he : {ω | a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧
        denseSeq ℝ≥0 j ≤ d ∧
          dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ) ∧
            c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖} =
        {ω | c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      tauto
    rw [he]
    have hi := (hX (denseSeq ℝ≥0 i)).mono
      (F.mono (hC.2.1.trans (hC.2.2.1.trans hdt))) le_rfl
    have hj := (hX (denseSeq ℝ≥0 j)).mono (F.mono (hC.2.2.1.trans hdt)) le_rfl
    exact measurableSet_lt measurable_const (hj.sub hi).norm
  · have he : {ω | a ≤ denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 i ≤ denseSeq ℝ≥0 j ∧
        denseSeq ℝ≥0 j ≤ d ∧
          dist (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) < 1 / (n + 1 : ℝ) ∧
            c < ‖X (denseSeq ℝ≥0 j) ω - X (denseSeq ℝ≥0 i) ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      tauto
    rw [he]
    exact MeasurableSet.empty

/-- Occurrence of a strict large jump in `(s,t)` is measurable at `t`.
The zero-time source jump is excluded by the interval, and an endpoint jump
at `t` is not part of this open-interval event. -/
theorem Adapted.measurableSet_exists_large_jump_Ioo (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (s t : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    MeasurableSet[F t] {ω | ∃ u : ℝ≥0, s < u ∧ u < t ∧
      b < ‖jumpProcess X u ω‖} := by
  classical
  let : MeasurableSpace Ω := F t
  have he : {ω | ∃ u : ℝ≥0, s < u ∧ u < t ∧ b < ‖jumpProcess X u ω‖} =
      {ω | ∃ c : ℚ, ∃ i j : ℕ,
        (b < (c : ℝ) ∧ s < denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 j < t) ∧
          HasArbitrarilyShortDenseIncrements (X · ω)
            (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) c} := by
    ext ω
    rw [Set.mem_ofPred_eq, (hc ω).exists_large_jump_Ioo_iff_dense_increments s t hb]
    constructor
    · rintro ⟨c, hbc, i, j, hsi, hjt, hinc⟩
      exact ⟨c, i, j, ⟨hbc, hsi, hjt⟩, hinc⟩
    · rintro ⟨c, i, j, ⟨hbc, hsi, hjt⟩, hinc⟩
      exact ⟨c, hbc, i, j, hsi, hjt, hinc⟩
  rw [he]
  simp_rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro c
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hC : b < (c : ℝ) ∧ s < denseSeq ℝ≥0 i ∧ denseSeq ℝ≥0 j < t
  · simp only [hC, true_and]
    exact hX.measurableSet_arbitrarilyShortDenseIncrements
      (denseSeq ℝ≥0 i) (denseSeq ℝ≥0 j) t hC.2.2.le c
  · simp only [hC, false_and]
    exact MeasurableSet.empty

end MeasureTheory
