/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.AdmissiblePartition
public import StochLean.Analysis.PathVariation.EndpointInvariance

/-! # Strict representatives of deterministic partitions

Sorting the actual endpoint set removes repetitions within the same `TimePartition`
owner. The existing endpoint-set invariance theorem then preserves every cell sum
with zero diagonal contribution. No new partition type or selected deduplication
operator is introduced. At horizon zero the strict representative is the existing
empty partition, whose endpoint list consists of the single value zero.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

/-- Every finite partition has a strictly increasing enumeration of the same endpoints. -/
theorem exists_strictMono_range_eq {T : ℝ≥0} (π : TimePartition T) :
    ∃ ρ : TimePartition T, StrictMono ρ.point ∧ Set.range ρ.point = Set.range π.point := by
  classical
  let s := Finset.univ.image π.point
  have h0 : 0 ∈ s := mem_image.mpr ⟨0, mem_univ _, π.first_eq_zero⟩
  have hT : T ∈ s := mem_image.mpr ⟨Fin.last π.size, mem_univ _, π.last_eq_horizon⟩
  have hb : ∀ t ∈ s, t ≤ T := by
    intro t ht
    obtain ⟨i, _, rfl⟩ := mem_image.mp ht
    exact π.point_le_horizon i
  refine ⟨ofFinset s h0 hT hb, ofFinset_strictMono s h0 hT hb, ?_⟩
  rw [ofFinset_range]
  simp [s]

/-- The only strict partition at horizon zero is the original empty partition. -/
theorem eq_empty_of_strictMono (π : TimePartition 0) (hπ : StrictMono π.point) :
    π = empty := by
  have he : Fin.last π.size = (0 : Fin (π.size + 1)) :=
    hπ.injective (π.last_eq_horizon.trans π.first_eq_zero.symm)
  have hs : π.size = 0 := congrArg Fin.val he
  cases π with
  | mk n p hm h0 hT =>
    change n = 0 at hs
    subst n
    have hp : p = fun _ ↦ 0 := by
      funext i
      have hi : i = 0 := by
        apply Fin.ext
        change i.val = 0
        have hil : i.val < 1 := i.isLt
        omega
      simpa only [hi] using h0
    subst p
    rfl

end StochLean.TimePartition
