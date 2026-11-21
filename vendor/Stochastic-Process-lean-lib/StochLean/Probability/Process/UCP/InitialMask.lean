/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP

/-! # Fixed event masks preserve UCP convergence

Outer-measure comparison needs no measurability of the event or of the paths.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem compactDeviation_indicator_le (s : Set Ω) (T : ℝ≥0) (ω : Ω) :
    compactDeviation (fun t ↦ s.indicator (X t)) (fun t ↦ s.indicator (Y t)) T ω ≤
      compactDeviation X Y T ω := by
  by_cases hs : ω ∈ s
  · simp only [compactDeviation, indicator_of_mem hs, le_refl]
  · simp only [compactDeviation, indicator_of_notMem hs, sub_self, norm_zero,
      ENNReal.ofReal_zero]
    exact iSup_le fun _ ↦ iSup_le fun _ ↦ bot_le

theorem TendstoUCP.indicator {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l Y) (s : Set Ω) :
    TendstoUCP P (fun n t ↦ s.indicator (Z n t)) l (fun t ↦ s.indicator (Y t)) := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T ε hε)
    (fun _ ↦ bot_le)
  intro n
  exact measure_mono fun ω hω ↦ hω.trans (compactDeviation_indicator_le s T ω)

end ProbabilityTheory
