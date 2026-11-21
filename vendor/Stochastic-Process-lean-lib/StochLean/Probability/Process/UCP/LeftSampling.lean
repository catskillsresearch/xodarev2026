/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.LeftSampling
public import StochLean.Analysis.PathVariation.LeftStepBounds
public import StochLean.Probability.Process.UCP

/-! # Left sampling is a compact-deviation contraction

The bound is uniform over arbitrary random partitions and requires no path
regularity or measurability. It does not assert that sampling a discontinuous
path on finer partitions converges uniformly to its left-limit process.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {l : Filter ι} {X Y : ℝ≥0 → Ω → ℝ}

@[simp] theorem StoppingTimePartition.leftSampleProcess_zero_process
    (π : StoppingTimePartition F) : π.leftSampleProcess (0 : ℝ≥0 → Ω → ℝ) = 0 := by
  funext t ω
  exact congrFun (π.path ω).leftStep_zero_fun t

theorem compactDeviation_leftSampleProcess_le (π : StoppingTimePartition F)
    (T : ℝ≥0) (ω : Ω) :
    compactDeviation (π.leftSampleProcess X) (π.leftSampleProcess Y) T ω ≤
      compactDeviation X Y T ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  change ENNReal.ofReal ‖(π.path ω).leftStep (X · ω) t - (π.path ω).leftStep (Y · ω) t‖ ≤ _
  by_cases ht0 : t = 0
  · subst t
    simpa only [StochLean.TimePartition.leftStep_zero] using enorm_sub_le_compactDeviation ht ω
  by_cases htπ : t ≤ π.terminal ω
  · obtain ⟨i, hi⟩ := (π.path ω).exists_cell ⟨pos_iff_ne_zero.mpr ht0, htπ⟩
    rw [(π.path ω).leftStep_eq_of_mem_cell (X · ω) hi,
      (π.path ω).leftStep_eq_of_mem_cell (Y · ω) hi]
    exact enorm_sub_le_compactDeviation (hi.1.le.trans ht) ω
  · rw [(π.path ω).leftStep_eq_zero_of_horizon_lt (X · ω) (lt_of_not_ge htπ),
      (π.path ω).leftStep_eq_zero_of_horizon_lt (Y · ω) (lt_of_not_ge htπ)]
    simp only [sub_self, norm_zero, ENNReal.ofReal_zero, zero_le]

theorem TendstoUCP.leftSampleProcess_zero {Z : ι → ℝ≥0 → Ω → ℝ}
    (hu : TendstoUCP P Z l 0) (π : ι → StoppingTimePartition F) :
    TendstoUCP P (fun n ↦ (π n).leftSampleProcess (Z n)) l 0 := by
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu T ε hε)
    (fun _ ↦ bot_le)
  intro n
  apply measure_mono
  intro ω hω
  change ε ≤ compactDeviation ((π n).leftSampleProcess (Z n)) 0 T ω at hω
  change ε ≤ compactDeviation (Z n) 0 T ω
  apply hω.trans
  simpa only [StoppingTimePartition.leftSampleProcess_zero_process] using
    (compactDeviation_leftSampleProcess_le (X := Z n) (Y := 0) (π n) T ω)

end ProbabilityTheory
