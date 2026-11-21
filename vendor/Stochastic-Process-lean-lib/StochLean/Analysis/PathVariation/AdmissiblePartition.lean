/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Locally finite deterministic partitions and finite-horizon restriction

An infinite partition is stored as its set of endpoints. Restriction to `[0,T]`
keeps every original endpoint in that interval and adds only `T`. Its sorted
enumeration belongs to the same finite `TimePartition` owner used by random
partitions. Admissibility uses the maximum adjacent gap, not the insufficient
nearest-neighbor mesh printed in Klenke 21.56; see the source-correction ledger.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal ENNReal Topology

namespace StochLean

namespace TimePartition

/-- Ordered enumeration of an endpoint set, including the singleton case `T=0`. -/
noncomputable def ofFinset {T : ℝ≥0} (s : Finset ℝ≥0)
    (h0 : 0 ∈ s) (hT : T ∈ s) (hb : ∀ x ∈ s, x ≤ T) : TimePartition T := by
  have hc : s.card = s.card - 1 + 1 :=
    (Nat.sub_add_cancel (card_pos.mpr ⟨0, h0⟩)).symm
  let e := s.orderEmbOfFin hc
  refine ⟨s.card - 1, e, e.monotone, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, e i = 0 := by
      change 0 ∈ Set.range (s.orderEmbOfFin hc)
      rw [s.range_orderEmbOfFin hc]
      exact h0
    exact le_antisymm ((e.monotone (Fin.zero_le i)).trans_eq hi) bot_le
  · apply le_antisymm (hb _ (s.orderEmbOfFin_mem hc _))
    obtain ⟨i, hi⟩ : ∃ i, e i = T := by
      change T ∈ Set.range (s.orderEmbOfFin hc)
      rw [s.range_orderEmbOfFin hc]
      exact hT
    exact hi ▸ e.monotone (Fin.le_last i)

theorem ofFinset_range {T : ℝ≥0} (s : Finset ℝ≥0)
    (h0 : 0 ∈ s) (hT : T ∈ s) (hb : ∀ x ∈ s, x ≤ T) :
    Set.range (ofFinset s h0 hT hb).point = (s : Set ℝ≥0) :=
  s.range_orderEmbOfFin _

theorem ofFinset_strictMono {T : ℝ≥0} (s : Finset ℝ≥0)
    (h0 : 0 ∈ s) (hT : T ∈ s) (hb : ∀ x ∈ s, x ≤ T) :
    StrictMono (ofFinset s h0 hT hb).point := (s.orderEmbOfFin _).strictMono

end TimePartition

/-- Endpoint data of a locally finite partition of the whole nonnegative line. -/
structure LocallyFinitePartition where
  points : Set ℝ≥0
  zero_mem : 0 ∈ points
  finite_bounded : ∀ T, (points ∩ Icc 0 T).Finite
  unbounded : ¬ BddAbove points

namespace LocallyFinitePartition

theorem countable (P : LocallyFinitePartition) : P.points.Countable := by
  apply (Set.countable_iUnion fun n : ℕ ↦ (P.finite_bounded n).countable).mono
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact mem_iUnion.mpr ⟨n, ht, bot_le, hn⟩

noncomputable def restrictFinset (P : LocallyFinitePartition) (T : ℝ≥0) : Finset ℝ≥0 :=
  insert T (P.finite_bounded T).toFinset

theorem mem_restrictFinset (P : LocallyFinitePartition) (T t : ℝ≥0) :
    t ∈ P.restrictFinset T ↔ t = T ∨ t ∈ P.points ∧ t ≤ T := by
  simp [restrictFinset]

theorem zero_mem_restrictFinset (P : LocallyFinitePartition) (T : ℝ≥0) :
    0 ∈ P.restrictFinset T :=
  (P.mem_restrictFinset T 0).mpr (Or.inr ⟨P.zero_mem, bot_le⟩)

theorem horizon_mem_restrictFinset (P : LocallyFinitePartition) (T : ℝ≥0) :
    T ∈ P.restrictFinset T := (P.mem_restrictFinset T T).mpr (Or.inl rfl)

theorem le_of_mem_restrictFinset (P : LocallyFinitePartition) (T t : ℝ≥0)
    (ht : t ∈ P.restrictFinset T) : t ≤ T := by
  rcases (P.mem_restrictFinset T t).mp ht with rfl | ht
  · exact le_rfl
  · exact ht.2

noncomputable def restrict (P : LocallyFinitePartition) (T : ℝ≥0) : TimePartition T :=
  TimePartition.ofFinset (P.restrictFinset T) (P.zero_mem_restrictFinset T)
    (P.horizon_mem_restrictFinset T) (P.le_of_mem_restrictFinset T)

/-- The finite representation neither loses source endpoints nor inserts an auxiliary grid. -/
theorem mem_range_restrict (P : LocallyFinitePartition) (T t : ℝ≥0) :
    t ∈ Set.range (P.restrict T).point ↔ t = T ∨ t ∈ P.points ∧ t ≤ T := by
  rw [restrict, TimePartition.ofFinset_range]
  exact P.mem_restrictFinset T t

theorem restrictFinset_mono {P Q : LocallyFinitePartition} (hPQ : P.points ⊆ Q.points)
    (T : ℝ≥0) : P.restrictFinset T ⊆ Q.restrictFinset T := by
  intro t ht
  rcases (P.mem_restrictFinset T t).mp ht with ht | ⟨ht, htT⟩
  · exact (Q.mem_restrictFinset T t).mpr (Or.inl ht)
  · exact (Q.mem_restrictFinset T t).mpr (Or.inr ⟨hPQ ht, htT⟩)

/-- Extended maximum adjacent gap over all finite horizons. No finiteness fallback is used. -/
noncomputable def mesh (P : LocallyFinitePartition) : ℝ≥0∞ :=
  ⨆ T : ℝ≥0, ((P.restrict T).mesh : ℝ≥0∞)

theorem restrict_mesh_le (P : LocallyFinitePartition) (T : ℝ≥0) :
    ((P.restrict T).mesh : ℝ≥0∞) ≤ P.mesh := by
  exact le_iSup (fun S : ℝ≥0 ↦ ((P.restrict S).mesh : ℝ≥0∞)) T

end LocallyFinitePartition

/-- Corrected Klenke admissibility: nested sets and vanishing maximum adjacent gap.
No summable mesh rate or prescribed refinement ratio is imposed. -/
def IsAdmissiblePartitionSequence (P : ℕ → LocallyFinitePartition) : Prop :=
  Monotone (fun n ↦ (P n).points) ∧ Tendsto (fun n ↦ (P n).mesh) atTop (𝓝 0)

/-- Mesh convergence is preserved even when the finite restriction horizon varies with `n`. -/
theorem IsAdmissiblePartitionSequence.restrict_mesh_tendsto {P : ℕ → LocallyFinitePartition}
    (hP : IsAdmissiblePartitionSequence P) (T : ℕ → ℝ≥0) :
    Tendsto (fun n ↦ ((P n).restrict (T n)).mesh) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n ↦ (((P n).restrict (T n)).mesh : ℝ≥0∞)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP.2
      (fun _ ↦ bot_le) (fun n ↦ (P n).restrict_mesh_le (T n))
  exact ENNReal.tendsto_coe.mp hlim

end StochLean
