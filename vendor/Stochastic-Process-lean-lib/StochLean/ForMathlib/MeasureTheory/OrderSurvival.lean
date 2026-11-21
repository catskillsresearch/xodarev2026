/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Topology.Order.IsLUB

/-! # Positive pre-jump survival at almost every sample

The samples whose closed upper tail has zero mass form a null set. If their
infimum belongs to the set, its null tail covers the set. Otherwise a countable
sequence from the set approaching its infimum supplies a countable null cover.

No atomlessness, finite measure or measurability of the tail function is used.
The closed endpoint is essential: an atom at the last possible sample is
included in its own survival mass.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace MeasureTheory

/-- In a first-countable complete linear order, the actual closed upper tail
has positive mass at almost every sample, including any terminal atom. -/
theorem ae_pos_measure_Ici {α : Type*} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α]
    [MeasurableSpace α] (μ : Measure α) : ∀ᵐ x ∂μ, 0 < μ (Ici x) := by
  classical
  let S : Set α := {x | μ (Ici x) = 0}
  have hnull : μ S = 0 := by
    by_cases hS : S.Nonempty
    · by_cases hinf : sInf S ∈ S
      · apply measure_mono_null (show S ⊆ Ici (sInf S) from fun x hx ↦ sInf_le hx)
        exact hinf
      · obtain ⟨u, _, hu, hmem⟩ := exists_seq_tendsto_sInf hS
          (show BddBelow S from ⟨⊥, fun _ _ ↦ bot_le⟩)
        have hcover : S ⊆ ⋃ n : ℕ, Ici (u n) := by
          intro x hx
          have hlt : sInf S < x := lt_of_le_of_ne (sInf_le hx)
            (fun he ↦ hinf (he.symm ▸ hx))
          obtain ⟨n, hn⟩ := (hu.eventually (Iio_mem_nhds hlt)).exists
          exact mem_iUnion.mpr ⟨n, hn.le⟩
        exact measure_mono_null hcover (measure_iUnion_null fun n ↦ hmem n)
    · rw [not_nonempty_iff_eq_empty.mp hS, measure_empty]
  rw [ae_iff]
  simpa only [not_lt, nonpos_iff_eq_zero] using hnull

end MeasureTheory
