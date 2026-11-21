/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Supremum

/-! # Countable representation of the full half-line supremum

Right continuity identifies the actual extended supremum over all times with
one countable dense supremum. No boundedness or real-valued fallback is used.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

theorem iSup_ofReal_eq_iSup_denseSeq_of_rightContinuous {f : ℝ≥0 → ℝ}
    (hf : IsRightContinuousPath f) :
    (⨆ t, ENNReal.ofReal (f t)) = ⨆ n, ENNReal.ofReal (f (TopologicalSpace.denseSeq ℝ≥0 n)) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hd : Dense (Set.range (TopologicalSpace.denseSeq ℝ≥0)) :=
      TopologicalSpace.denseRange_denseSeq ℝ≥0
    obtain ⟨u, _, hu, hl⟩ := hd.exists_seq_strictAnti_tendsto t
    have hw : Tendsto u atTop (nhdsWithin t (Set.Ici t)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hl, Eventually.of_forall fun n ↦ show t ≤ u n from (hu n).1.le⟩
    apply le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto (f t)).comp
      ((hf t).tendsto.comp hw))
    intro n
    obtain ⟨k, hk⟩ := (hu n).2
    simpa only [hk, Function.comp_apply] using
      le_iSup (fun k ↦ ENNReal.ofReal (f (TopologicalSpace.denseSeq ℝ≥0 k))) k
  · exact iSup_le fun n ↦ le_iSup (fun t ↦ ENNReal.ofReal (f t)) _

theorem aemeasurable_iSup_ofReal_of_rightContinuous
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (X t)) (hr : HasRightContinuousPaths X P) :
    AEMeasurable (fun ω ↦ ⨆ t, ENNReal.ofReal (X t ω)) P := by
  have hd : Measurable (fun ω ↦ ⨆ n,
      ENNReal.ofReal (X (TopologicalSpace.denseSeq ℝ≥0 n) ω)) :=
    Measurable.iSup fun n ↦ ENNReal.measurable_ofReal.comp (hm _)
  apply hd.aemeasurable.congr
  filter_upwards [hr] with ω hω
  exact (iSup_ofReal_eq_iSup_denseSeq_of_rightContinuous hω).symm

end ProbabilityTheory
