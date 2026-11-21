/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.AdmissiblePartition
public import StochLean.Probability.Process.Partition

/-! # Klenke partitions as Protter stopping-time partitions

Finite restriction is lossless on each chosen horizon. This bridge imposes
neither a summable mesh rate nor new grid points inside a source cell.
It does not assert the still-separate general stochastic QV approximation.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem StoppingTimePartition.isTendingToIdentity_of_klenke
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π)
    {T : ℕ → ℝ≥0} (hT : Tendsto T atTop atTop) :
    IsTendingToIdentity (fun n ↦ deterministic F ((π n).restrict (T n))) P :=
  isTendingToIdentity_deterministic (fun n ↦ (π n).restrict (T n)) hT
    (hπ.restrict_mesh_tendsto T)

end ProbabilityTheory
