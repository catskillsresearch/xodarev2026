/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Separation.Hausdorff

/-! # Compact exhaustion of an open domain with a fixed base point

This transports Mathlib's compact exhaustion of the open subtype to the
ambient space and includes a prescribed point in every region. Every compact
subset of the domain is eventually contained in all later regions.
-/

@[expose] public section

open Set

namespace StochLean

theorem exists_compact_exhaustion_with_basepoint
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    [SecondCountableTopology E] {D : Set E} (hD : IsOpen D) {c : E} (hc : c ∈ D) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n) ∧ c ∈ K n ∧ K n ⊆ D) ∧ Monotone K ∧
      ∀ C : Set E, IsCompact C → C ⊆ D → ∃ N, ∀ n ≥ N, C ⊆ K n := by
  let : LocallyCompactSpace D := hD.locallyCompactSpace
  let L := CompactExhaustion.choice D
  let K := fun n ↦ (Subtype.val '' L n : Set E) ∪ {c}
  refine ⟨K, fun n ↦ ?_, ?_, ?_⟩
  · refine ⟨((L.isCompact n).image continuous_subtype_val).union isCompact_singleton,
      Or.inr (mem_singleton c), ?_⟩
    rintro x (⟨y, _, rfl⟩ | hx)
    · exact y.property
    · exact (mem_singleton_iff.mp hx) ▸ hc
  · intro n m hnm
    exact union_subset_union (image_mono (L.subset hnm)) subset_rfl
  · intro C hC hCD
    have hsub : IsCompact ((Subtype.val : D → E) ⁻¹' C) := by
      rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
        inter_eq_left.mpr hCD]
      exact hC
    obtain ⟨N, hN⟩ := L.exists_superset_of_isCompact hsub
    refine ⟨N, fun n hn x hx ↦ Or.inl ?_⟩
    exact ⟨⟨x, hCD hx⟩, L.subset hn (hN hx), rfl⟩

end StochLean
